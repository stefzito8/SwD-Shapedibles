package model.datasource;

import categories.IntegrationTest;
import integration.H2TestDatabase;
import model.bean.OrderBean;
import org.junit.jupiter.api.*;

import javax.sql.DataSource;
import java.sql.SQLException;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Integration tests for OrderDaoDataSource.
 * 
 * Testing Level: Integration
 * Technique: White-Box (Branch Coverage) with H2 Database
 * 
 * ============================================================================
 * BRANCH STRUCTURE
 * ============================================================================
 * 
 * Method: doRetrieveByKey(String user, int id)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | ODS-B1    | rs.next()                    | Populate bean     | Return default |
 * -----------------------------------------------------------------
 * 
 * Method: doDelete(String user, int id)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | ODS-B2    | result != 0                  | Return true       | Return false   |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveAll(String order)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | ODS-B3    | order != null && !order.equals("") | Add ORDER BY | No ORDER BY  |
 * | ODS-B4    | rs.next() loop               | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveByUser(String user)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | ODS-B5    | rs.next() loop               | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@IntegrationTest
@DisplayName("OrderDaoDataSource Integration Tests")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public class OrderDaoDataSourceTest {

    private static DataSource dataSource;
    private OrderDaoDataSource orderDao;

    @BeforeAll
    static void setUpClass() {
        dataSource = H2TestDatabase.getDataSource();
        H2TestDatabase.initializeDatabase();
    }

    @BeforeEach
    void setUp() {
        H2TestDatabase.resetDatabase();
        orderDao = new OrderDaoDataSource(dataSource);
    }

    @AfterAll
    static void tearDownClass() {
        H2TestDatabase.resetDatabase();
    }

    // ============================================================================
    // doSave Tests
    // ============================================================================

    @Nested
    @DisplayName("doSave Tests")
    class DoSaveTests {

        @Test
        @DisplayName("Save new order successfully")
        void testSaveNewOrder() throws SQLException {
            OrderBean order = createTestOrder("customer1", 1, "Via Roma 42", "PENDING", "2024-01-15", 99.99);

            orderDao.doSave(order);

            OrderBean retrieved = orderDao.doRetrieveByKey("customer1", 1);
            assertNotNull(retrieved);
            assertEquals("customer1", retrieved.getUtente());
            assertEquals(1, retrieved.getCodice());
            assertEquals(99.99, retrieved.getSaldoTotale(), 0.001);
        }

        @Test
        @DisplayName("Save order with all fields")
        void testSaveOrderAllFields() throws SQLException {
            OrderBean order = createTestOrder("user1", 100, "123 Main St, NYC", "COMPLETED", "2024-01-20", 250.50);

            orderDao.doSave(order);

            OrderBean retrieved = orderDao.doRetrieveByKey("user1", 100);
            assertEquals("123 Main St, NYC", retrieved.getIndirizzo());
            assertEquals("COMPLETED", retrieved.getStato());
            assertEquals("2024-01-20", retrieved.getDataOrdine());
        }

        @Test
        @DisplayName("Save order with zero total")
        void testSaveOrderZeroTotal() throws SQLException {
            OrderBean order = createTestOrder("user1", 1, "Address", "PENDING", "2024-01-15", 0.0);

            orderDao.doSave(order);

            OrderBean retrieved = orderDao.doRetrieveByKey("user1", 1);
            assertEquals(0.0, retrieved.getSaldoTotale(), 0.001);
        }

        @Test
        @DisplayName("Save multiple orders for same user")
        void testSaveMultipleOrdersSameUser() throws SQLException {
            orderDao.doSave(createTestOrder("user1", 1, "Address1", "PENDING", "2024-01-15", 50.0));
            orderDao.doSave(createTestOrder("user1", 2, "Address2", "COMPLETED", "2024-01-16", 75.0));

            Collection<OrderBean> orders = orderDao.doRetrieveByUser("user1");
            assertEquals(2, orders.size());
        }
    }

    // ============================================================================
    // doRetrieveByKey Tests (Branch ODS-B1)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByKey Tests")
    class DoRetrieveByKeyTests {

        @Test
        @DisplayName("B1-True: Retrieve existing order populates bean")
        void testRetrieveExistingOrder() throws SQLException {
            orderDao.doSave(createTestOrder("customer1", 1, "Via Roma 42", "PENDING", "2024-01-15", 99.99));

            OrderBean retrieved = orderDao.doRetrieveByKey("customer1", 1);

            assertNotNull(retrieved);
            assertEquals("customer1", retrieved.getUtente());
            assertEquals(1, retrieved.getCodice());
            assertEquals("PENDING", retrieved.getStato());
        }

        @Test
        @DisplayName("B1-False: Retrieve non-existent order returns default bean")
        void testRetrieveNonExistentOrder() throws SQLException {
            OrderBean retrieved = orderDao.doRetrieveByKey("nonexistent", 999);

            assertNotNull(retrieved);
            assertEquals(" ", retrieved.getUtente()); // Default value
            assertEquals(0, retrieved.getCodice()); // Default value
        }

        @Test
        @DisplayName("Retrieve with wrong user returns default bean")
        void testRetrieveWrongUser() throws SQLException {
            orderDao.doSave(createTestOrder("customer1", 1, "Address", "PENDING", "2024-01-15", 50.0));

            OrderBean retrieved = orderDao.doRetrieveByKey("wronguser", 1);

            assertNotNull(retrieved);
            assertEquals(" ", retrieved.getUtente());
        }

        @Test
        @DisplayName("Retrieve with wrong code returns default bean")
        void testRetrieveWrongCode() throws SQLException {
            orderDao.doSave(createTestOrder("customer1", 1, "Address", "PENDING", "2024-01-15", 50.0));

            OrderBean retrieved = orderDao.doRetrieveByKey("customer1", 999);

            assertNotNull(retrieved);
            assertEquals(0, retrieved.getCodice());
        }
    }

    // ============================================================================
    // doDelete Tests (Branch ODS-B2)
    // ============================================================================

    @Nested
    @DisplayName("doDelete Tests")
    class DoDeleteTests {

        @Test
        @DisplayName("B2-True: Delete existing order returns true")
        void testDeleteExistingOrder() throws SQLException {
            orderDao.doSave(createTestOrder("customer1", 1, "Address", "PENDING", "2024-01-15", 50.0));

            boolean result = orderDao.doDelete("customer1", 1);

            assertTrue(result);
            // Verify deletion
            OrderBean retrieved = orderDao.doRetrieveByKey("customer1", 1);
            assertEquals(" ", retrieved.getUtente());
        }

        @Test
        @DisplayName("B2-False: Delete non-existent order returns false")
        void testDeleteNonExistentOrder() throws SQLException {
            boolean result = orderDao.doDelete("nonexistent", 999);

            assertFalse(result);
        }

        @Test
        @DisplayName("Delete with wrong user returns false")
        void testDeleteWrongUser() throws SQLException {
            orderDao.doSave(createTestOrder("customer1", 1, "Address", "PENDING", "2024-01-15", 50.0));

            boolean result = orderDao.doDelete("wronguser", 1);

            assertFalse(result);
            // Original order should still exist
            OrderBean retrieved = orderDao.doRetrieveByKey("customer1", 1);
            assertEquals("customer1", retrieved.getUtente());
        }

        @Test
        @DisplayName("Delete with wrong code returns false")
        void testDeleteWrongCode() throws SQLException {
            orderDao.doSave(createTestOrder("customer1", 1, "Address", "PENDING", "2024-01-15", 50.0));

            boolean result = orderDao.doDelete("customer1", 999);

            assertFalse(result);
        }
    }

    // ============================================================================
    // doRetrieveAll Tests (Branches ODS-B3, ODS-B4)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveAll Tests")
    class DoRetrieveAllTests {

        @Test
        @DisplayName("B3-False, B4-False: Retrieve all from empty table")
        void testRetrieveAllEmpty() throws SQLException {
            Collection<OrderBean> orders = orderDao.doRetrieveAll(null);

            assertNotNull(orders);
            assertTrue(orders.isEmpty());
        }

        @Test
        @DisplayName("B3-False, B4-True: Retrieve all without order")
        void testRetrieveAllWithoutOrder() throws SQLException {
            orderDao.doSave(createTestOrder("user1", 1, "Addr1", "PENDING", "2024-01-15", 50.0));
            orderDao.doSave(createTestOrder("user2", 2, "Addr2", "COMPLETED", "2024-01-16", 100.0));

            Collection<OrderBean> orders = orderDao.doRetrieveAll(null);

            assertEquals(2, orders.size());
        }

        @Test
        @DisplayName("B3-True, B4-True: Retrieve all with order by code")
        void testRetrieveAllWithOrder() throws SQLException {
            orderDao.doSave(createTestOrder("user1", 2, "Addr1", "PENDING", "2024-01-15", 50.0));
            orderDao.doSave(createTestOrder("user2", 1, "Addr2", "COMPLETED", "2024-01-16", 100.0));

            Collection<OrderBean> orders = orderDao.doRetrieveAll("code");

            assertEquals(2, orders.size());
            // First order should have code 1 when ordered
            OrderBean first = orders.iterator().next();
            assertEquals(1, first.getCodice());
        }

        @Test
        @DisplayName("B3-False: Retrieve all with empty order string")
        void testRetrieveAllEmptyOrder() throws SQLException {
            orderDao.doSave(createTestOrder("user1", 1, "Addr1", "PENDING", "2024-01-15", 50.0));

            Collection<OrderBean> orders = orderDao.doRetrieveAll("");

            assertEquals(1, orders.size());
        }

        @Test
        @DisplayName("Retrieve all orders with different states")
        void testRetrieveAllDifferentStates() throws SQLException {
            orderDao.doSave(createTestOrder("user1", 1, "Addr", "PENDING", "2024-01-15", 50.0));
            orderDao.doSave(createTestOrder("user2", 2, "Addr", "COMPLETED", "2024-01-16", 75.0));
            orderDao.doSave(createTestOrder("user3", 3, "Addr", "SHIPPED", "2024-01-17", 100.0));

            Collection<OrderBean> orders = orderDao.doRetrieveAll(null);

            assertEquals(3, orders.size());
            assertTrue(orders.stream().anyMatch(o -> "PENDING".equals(o.getStato())));
            assertTrue(orders.stream().anyMatch(o -> "COMPLETED".equals(o.getStato())));
            assertTrue(orders.stream().anyMatch(o -> "SHIPPED".equals(o.getStato())));
        }

        @Test
        @DisplayName("Verify all fields are populated in doRetrieveAll")
        void testRetrieveAllVerifiesAllFields() throws SQLException {
            orderDao.doSave(createTestOrder("verifyuser", 42, "123 Verify Street", "PROCESSING", "2024-06-15", 199.99));

            Collection<OrderBean> orders = orderDao.doRetrieveAll(null);
            OrderBean retrieved = orders.iterator().next();

            // Assertions on ALL fields to kill setter mutations
            assertEquals("verifyuser", retrieved.getUtente());
            assertEquals(42, retrieved.getCodice());
            assertEquals("123 Verify Street", retrieved.getIndirizzo());
            assertEquals("PROCESSING", retrieved.getStato());
            assertEquals("2024-06-15", retrieved.getDataOrdine());
            assertEquals(199.99, retrieved.getSaldoTotale(), 0.001);
        }
    }

    // ============================================================================
    // doRetrieveByUser Tests (Branch ODS-B5)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByUser Tests")
    class DoRetrieveByUserTests {

        @Test
        @DisplayName("B5-True: Retrieve orders for user with multiple orders")
        void testRetrieveByUserMultiple() throws SQLException {
            orderDao.doSave(createTestOrder("customer1", 1, "Addr1", "PENDING", "2024-01-15", 50.0));
            orderDao.doSave(createTestOrder("customer1", 2, "Addr2", "COMPLETED", "2024-01-16", 75.0));
            orderDao.doSave(createTestOrder("customer2", 3, "Addr3", "PENDING", "2024-01-17", 100.0));

            Collection<OrderBean> orders = orderDao.doRetrieveByUser("customer1");

            assertEquals(2, orders.size());
            assertTrue(orders.stream().allMatch(o -> "customer1".equals(o.getUtente())));
        }

        @Test
        @DisplayName("B5-False: Retrieve orders for non-existent user")
        void testRetrieveByUserNonExistent() throws SQLException {
            Collection<OrderBean> orders = orderDao.doRetrieveByUser("nonexistent");

            assertNotNull(orders);
            assertTrue(orders.isEmpty());
        }

        @Test
        @DisplayName("Retrieve orders for user with single order")
        void testRetrieveByUserSingle() throws SQLException {
            orderDao.doSave(createTestOrder("singleuser", 1, "Address", "PENDING", "2024-01-15", 50.0));

            Collection<OrderBean> orders = orderDao.doRetrieveByUser("singleuser");

            assertEquals(1, orders.size());
        }

        @Test
        @DisplayName("Retrieve orders with empty username")
        void testRetrieveByUserEmpty() throws SQLException {
            Collection<OrderBean> orders = orderDao.doRetrieveByUser("");

            assertNotNull(orders);
            assertTrue(orders.isEmpty());
        }

        @Test
        @DisplayName("Verify all fields are populated in doRetrieveByUser")
        void testRetrieveByUserVerifiesAllFields() throws SQLException {
            orderDao.doSave(createTestOrder("fieldtestuser", 77, "456 Test Avenue", "SHIPPED", "2024-07-20", 349.50));

            Collection<OrderBean> orders = orderDao.doRetrieveByUser("fieldtestuser");
            OrderBean retrieved = orders.iterator().next();

            // Assertions on ALL fields to kill setter mutations
            assertEquals("fieldtestuser", retrieved.getUtente());
            assertEquals(77, retrieved.getCodice());
            assertEquals("456 Test Avenue", retrieved.getIndirizzo());
            assertEquals("SHIPPED", retrieved.getStato());
            assertEquals("2024-07-20", retrieved.getDataOrdine());
            assertEquals(349.50, retrieved.getSaldoTotale(), 0.001);
        }
    }

    // ============================================================================
    // Loop Boundary Tests
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("Loop: 0 iterations (no orders)")
        void testLoopZeroIterations() throws SQLException {
            Collection<OrderBean> orders = orderDao.doRetrieveAll(null);
            assertEquals(0, orders.size());
        }

        @Test
        @DisplayName("Loop: 1 iteration (single order)")
        void testLoopOneIteration() throws SQLException {
            orderDao.doSave(createTestOrder("user1", 1, "Address", "PENDING", "2024-01-15", 50.0));

            Collection<OrderBean> orders = orderDao.doRetrieveAll(null);
            assertEquals(1, orders.size());
        }

        @Test
        @DisplayName("Loop: >1 iterations (multiple orders)")
        void testLoopMultipleIterations() throws SQLException {
            for (int i = 1; i <= 10; i++) {
                orderDao.doSave(createTestOrder("user" + i, i, "Address" + i, "PENDING", 
                    "2024-01-" + String.format("%02d", i), i * 10.0));
            }

            Collection<OrderBean> orders = orderDao.doRetrieveAll(null);
            assertEquals(10, orders.size());
        }
    }

    // ============================================================================
    // Boundary Value Tests for Total
    // ============================================================================

    @Nested
    @DisplayName("Total Amount Boundary Tests")
    class TotalBoundaryTests {

        @Test
        @DisplayName("BV: Minimum total = 0.0")
        void testMinimumTotal() throws SQLException {
            orderDao.doSave(createTestOrder("user1", 1, "Addr", "PENDING", "2024-01-15", 0.0));

            OrderBean retrieved = orderDao.doRetrieveByKey("user1", 1);
            assertEquals(0.0, retrieved.getSaldoTotale(), 0.001);
        }

        @Test
        @DisplayName("BV: Small total = 0.01")
        void testSmallTotal() throws SQLException {
            orderDao.doSave(createTestOrder("user1", 1, "Addr", "PENDING", "2024-01-15", 0.01));

            OrderBean retrieved = orderDao.doRetrieveByKey("user1", 1);
            assertEquals(0.01, retrieved.getSaldoTotale(), 0.001);
        }

        @Test
        @DisplayName("BV: Large total")
        void testLargeTotal() throws SQLException {
            orderDao.doSave(createTestOrder("user1", 1, "Addr", "PENDING", "2024-01-15", 999999.99));

            OrderBean retrieved = orderDao.doRetrieveByKey("user1", 1);
            assertEquals(999999.99, retrieved.getSaldoTotale(), 0.01);
        }
    }

    // ============================================================================
    // Mutation Killer Tests
    // ============================================================================

    @Nested
    @DisplayName("Mutation Killer Tests")
    class MutationKillerTests {
        
        @Test
        @DisplayName("doSave actually persists data - kills VoidMethodCallMutator line 50")
        void testDoSaveActuallyPersists() throws SQLException {
            OrderBean order = createTestOrder("mutuser", 1001, "Mut Address", "PENDING", "2024-01-01", 99.99);
            
            // Verify empty before save
            Collection<OrderBean> beforeSave = orderDao.doRetrieveAll(null);
            assertEquals(0, beforeSave.size(), "Should be empty before save");
            
            // Save the order
            orderDao.doSave(order);
            
            // Verify present after save
            Collection<OrderBean> afterSave = orderDao.doRetrieveAll(null);
            assertEquals(1, afterSave.size(), "Should have 1 order after save");
            
            // Verify correct data was saved
            OrderBean saved = afterSave.iterator().next();
            assertEquals("mutuser", saved.getUtente());
            assertEquals("PENDING", saved.getStato());
            assertEquals(99.99, saved.getSaldoTotale(), 0.01);
        }
        
        @Test
        @DisplayName("doDelete actually removes data - kills NegateConditionalsMutator line 78")
        void testDoDeleteActuallyRemoves() throws SQLException {
            // First save an order
            orderDao.doSave(createTestOrder("deluser", 2001, "Del Address", "NEW", "2024-02-01", 50.00));
            
            // Get the saved order to find its code
            Collection<OrderBean> afterSave = orderDao.doRetrieveAll(null);
            assertEquals(1, afterSave.size());
            OrderBean saved = afterSave.iterator().next();
            
            // Delete it
            boolean result = orderDao.doDelete(saved.getUtente(), saved.getCodice());
            
            // Both the return value AND the actual deletion matter
            assertTrue(result, "doDelete should return true");
            
            // Verify it was actually deleted
            Collection<OrderBean> afterDelete = orderDao.doRetrieveAll(null);
            assertEquals(0, afterDelete.size(), "Should be empty after delete");
        }
        
        @Test
        @DisplayName("doDelete return value matches reality - kills return value mutations")
        void testDoDeleteReturnValueMatchesReality() throws SQLException {
            // Delete non-existent returns false
            boolean falseResult = orderDao.doDelete("nonexistent", 99999);
            assertFalse(falseResult, "Deleting non-existent should return false");
            
            // Add an order
            orderDao.doSave(createTestOrder("retuser", 3001, "Ret Address", "NEW", "2024-03-01", 75.00));
            Collection<OrderBean> afterSave = orderDao.doRetrieveAll(null);
            OrderBean saved = afterSave.iterator().next();
            
            // Delete existing returns true AND actually removes
            boolean trueResult = orderDao.doDelete(saved.getUtente(), saved.getCodice());
            assertTrue(trueResult, "Deleting existing should return true");
            assertTrue(orderDao.doRetrieveAll(null).isEmpty(), "Order should be gone");
        }
        
        @Test
        @DisplayName("doRetrieveAll returns correct collection - kills EmptyObjectReturnValsMutator line 158")
        void testDoRetrieveAllReturnsCorrectCollection() throws SQLException {
            orderDao.doSave(createTestOrder("user1", 4001, "Address1", "NEW", "2024-04-01", 10.00));
            orderDao.doSave(createTestOrder("user2", 4002, "Address2", "SHIPPED", "2024-04-02", 20.00));
            orderDao.doSave(createTestOrder("user3", 4003, "Address3", "DELIVERED", "2024-04-03", 30.00));
            
            Collection<OrderBean> result = orderDao.doRetrieveAll(null);
            
            // Must use the returned collection
            assertNotNull(result, "Result must not be null");
            assertFalse(result.isEmpty(), "Result must not be empty");
            assertEquals(3, result.size(), "Must have 3 orders");
        }
        
        @Test
        @DisplayName("doRetrieveByKey returns correct order - kills NegateConditionalsMutator line 115")
        void testDoRetrieveByKeyReturnsCorrectOrder() throws SQLException {
            orderDao.doSave(createTestOrder("keyuser", 5001, "Key Address", "PROCESSING", "2024-05-01", 123.45));
            
            // Get the saved order to find its actual code (since it's auto-generated)
            Collection<OrderBean> allOrders = orderDao.doRetrieveAll(null);
            OrderBean saved = allOrders.iterator().next();
            
            OrderBean result = orderDao.doRetrieveByKey(saved.getUtente(), saved.getCodice());
            
            assertNotNull(result);
            assertEquals(saved.getCodice(), result.getCodice());
            assertEquals("keyuser", result.getUtente());
            assertEquals("Key Address", result.getIndirizzo());
            assertEquals("PROCESSING", result.getStato());
        }
        
        @Test
        @DisplayName("doRetrieveByUser returns orders for specific user - kills NegateConditionalsMutator line 198")
        void testDoRetrieveByUserReturnsSpecificUserOnly() throws SQLException {
            orderDao.doSave(createTestOrder("userA", 6001, "AddressA1", "NEW", "2024-06-01", 100.00));
            orderDao.doSave(createTestOrder("userA", 6002, "AddressA2", "NEW", "2024-06-02", 200.00));
            orderDao.doSave(createTestOrder("userB", 6003, "AddressB1", "NEW", "2024-06-03", 300.00));
            
            Collection<OrderBean> userAOrders = orderDao.doRetrieveByUser("userA");
            
            assertEquals(2, userAOrders.size(), "UserA should have 2 orders");
            for (OrderBean order : userAOrders) {
                assertEquals("userA", order.getUtente(), "All orders should belong to userA");
                assertNotEquals("userB", order.getUtente());
            }
        }
    }

    // ============================================================================
    // Helper Methods
    // ============================================================================

    private OrderBean createTestOrder(String user, int code, String address, String state, 
                                      String date, double total) {
        OrderBean order = new OrderBean();
        order.setUtente(user);
        order.setCodice(code);
        order.setIndirizzo(address);
        order.setStato(state);
        order.setDataOrdine(date);
        order.setSaldoTotale(total);
        return order;
    }
}
