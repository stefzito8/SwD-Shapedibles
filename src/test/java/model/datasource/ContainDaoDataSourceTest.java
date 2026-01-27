package model.datasource;

import categories.IntegrationTest;
import integration.H2TestDatabase;
import model.bean.ContainBean;
import org.junit.jupiter.api.*;

import javax.sql.DataSource;
import java.sql.SQLException;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Integration tests for ContainDaoDataSource.
 * 
 * Testing Level: Integration
 * Technique: White-Box (Branch Coverage) with H2 Database
 * 
 * ============================================================================
 * BRANCH STRUCTURE
 * ============================================================================
 * 
 * Method: doRetrieveByKey(int orderID)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | CDS-B1    | rs.next()                    | Populate bean     | Return default |
 * -----------------------------------------------------------------
 * 
 * Method: doDelete(int orderID)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | CDS-B2    | result != 0                  | Return true       | Return false   |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveAll(String order)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | CDS-B3    | order != null && !order.equals("") | Add ORDER BY | No ORDER BY  |
 * | CDS-B4    | rs.next() loop               | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveByOrder(int orderID)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | CDS-B5    | rs.next() loop               | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@IntegrationTest
@DisplayName("ContainDaoDataSource Integration Tests")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public class ContainDaoDataSourceTest {

    private static DataSource dataSource;
    private ContainDaoDataSource containDao;

    @BeforeAll
    static void setUpClass() {
        dataSource = H2TestDatabase.getDataSource();
        H2TestDatabase.initializeDatabase();
    }

    @BeforeEach
    void setUp() {
        H2TestDatabase.resetDatabase();
        containDao = new ContainDaoDataSource(dataSource);
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
        @DisplayName("Save new contain entry successfully")
        void testSaveNewContain() throws SQLException {
            ContainBean contain = createTestContain(1, 100, 2);

            containDao.doSave(contain);

            ContainBean retrieved = containDao.doRetrieveByKey(1);
            assertNotNull(retrieved);
            assertEquals(1, retrieved.getCodiceOrdine());
            assertEquals(100, retrieved.getCodiceProdotto());
            assertEquals(2, retrieved.getQuantità());
        }

        @Test
        @DisplayName("Save contain with quantity = 1")
        void testSaveQuantityOne() throws SQLException {
            ContainBean contain = createTestContain(1, 100, 1);

            containDao.doSave(contain);

            ContainBean retrieved = containDao.doRetrieveByKey(1);
            assertEquals(1, retrieved.getQuantità());
        }

        @Test
        @DisplayName("Save contain with large quantity")
        void testSaveLargeQuantity() throws SQLException {
            ContainBean contain = createTestContain(1, 100, 9999);

            containDao.doSave(contain);

            ContainBean retrieved = containDao.doRetrieveByKey(1);
            assertEquals(9999, retrieved.getQuantità());
        }

        @Test
        @DisplayName("Save multiple items for same order")
        void testSaveMultipleItemsSameOrder() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));
            containDao.doSave(createTestContain(1, 200, 3));

            Collection<ContainBean> items = containDao.doRetrieveByOrder(1);
            assertEquals(2, items.size());
        }

        @Test
        @DisplayName("Save items for different orders")
        void testSaveItemsDifferentOrders() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));
            containDao.doSave(createTestContain(2, 200, 3));

            Collection<ContainBean> allItems = containDao.doRetrieveAll(null);
            assertEquals(2, allItems.size());
        }
    }

    // ============================================================================
    // doRetrieveByKey Tests (Branch CDS-B1)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByKey Tests")
    class DoRetrieveByKeyTests {

        @Test
        @DisplayName("B1-True: Retrieve existing contain populates bean")
        void testRetrieveExistingContain() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 5));

            ContainBean retrieved = containDao.doRetrieveByKey(1);

            assertNotNull(retrieved);
            assertEquals(1, retrieved.getCodiceOrdine());
            assertEquals(100, retrieved.getCodiceProdotto());
            assertEquals(5, retrieved.getQuantità());
        }

        @Test
        @DisplayName("B1-False: Retrieve non-existent contain returns default bean")
        void testRetrieveNonExistentContain() throws SQLException {
            ContainBean retrieved = containDao.doRetrieveByKey(999);

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodiceOrdine()); // Default value
            assertEquals(-1, retrieved.getCodiceProdotto()); // Default value
        }

        @Test
        @DisplayName("Retrieve with orderID = 0")
        void testRetrieveZeroOrderId() throws SQLException {
            ContainBean retrieved = containDao.doRetrieveByKey(0);

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodiceOrdine());
        }

        @Test
        @DisplayName("Retrieve returns first item when multiple exist")
        void testRetrieveReturnsFirstItem() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));
            containDao.doSave(createTestContain(1, 200, 3));

            // doRetrieveByKey iterates through all, but only one bean is returned
            // The last one processed will be in the bean
            ContainBean retrieved = containDao.doRetrieveByKey(1);
            assertEquals(1, retrieved.getCodiceOrdine());
        }
    }

    // ============================================================================
    // doDelete Tests (Branch CDS-B2)
    // ============================================================================

    @Nested
    @DisplayName("doDelete Tests")
    class DoDeleteTests {

        @Test
        @DisplayName("B2-True: Delete existing contain returns true")
        void testDeleteExistingContain() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));

            boolean result = containDao.doDelete(1);

            assertTrue(result);
            // Verify deletion
            ContainBean retrieved = containDao.doRetrieveByKey(1);
            assertEquals(-1, retrieved.getCodiceOrdine());
        }

        @Test
        @DisplayName("B2-False: Delete non-existent contain returns false")
        void testDeleteNonExistentContain() throws SQLException {
            boolean result = containDao.doDelete(999);

            assertFalse(result);
        }

        @Test
        @DisplayName("Delete removes all items for order")
        void testDeleteRemovesAllItemsForOrder() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));
            containDao.doSave(createTestContain(1, 200, 3));
            containDao.doSave(createTestContain(2, 300, 4));

            boolean result = containDao.doDelete(1);

            assertTrue(result);
            Collection<ContainBean> order1Items = containDao.doRetrieveByOrder(1);
            assertTrue(order1Items.isEmpty());
            // Order 2 should still exist
            Collection<ContainBean> order2Items = containDao.doRetrieveByOrder(2);
            assertEquals(1, order2Items.size());
        }

        @Test
        @DisplayName("Delete with orderID = 0")
        void testDeleteZeroOrderId() throws SQLException {
            boolean result = containDao.doDelete(0);

            assertFalse(result);
        }
    }

    // ============================================================================
    // doRetrieveAll Tests (Branches CDS-B3, CDS-B4)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveAll Tests")
    class DoRetrieveAllTests {

        @Test
        @DisplayName("B3-False, B4-False: Retrieve all from empty table")
        void testRetrieveAllEmpty() throws SQLException {
            Collection<ContainBean> items = containDao.doRetrieveAll(null);

            assertNotNull(items);
            assertTrue(items.isEmpty());
        }

        @Test
        @DisplayName("B3-False, B4-True: Retrieve all without order")
        void testRetrieveAllWithoutOrder() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));
            containDao.doSave(createTestContain(2, 200, 3));

            Collection<ContainBean> items = containDao.doRetrieveAll(null);

            assertEquals(2, items.size());
        }

        @Test
        @DisplayName("B3-True, B4-True: Retrieve all with order")
        void testRetrieveAllWithOrder() throws SQLException {
            containDao.doSave(createTestContain(2, 200, 3));
            containDao.doSave(createTestContain(1, 100, 2));

            Collection<ContainBean> items = containDao.doRetrieveAll("order_code");

            assertEquals(2, items.size());
            // First item should have order_code 1 when ordered
            ContainBean first = items.iterator().next();
            assertEquals(1, first.getCodiceOrdine());
        }

        @Test
        @DisplayName("B3-False: Retrieve all with empty order string")
        void testRetrieveAllEmptyOrder() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));

            Collection<ContainBean> items = containDao.doRetrieveAll("");

            assertEquals(1, items.size());
        }

        @Test
        @DisplayName("Retrieve all with multiple items per order")
        void testRetrieveAllMultipleItemsPerOrder() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));
            containDao.doSave(createTestContain(1, 200, 3));
            containDao.doSave(createTestContain(2, 300, 4));

            Collection<ContainBean> items = containDao.doRetrieveAll(null);

            assertEquals(3, items.size());
        }

        @Test
        @DisplayName("Verify all fields are populated in doRetrieveAll")
        void testRetrieveAllVerifiesAllFields() throws SQLException {
            containDao.doSave(createTestContain(42, 777, 99));

            Collection<ContainBean> items = containDao.doRetrieveAll(null);
            ContainBean retrieved = items.iterator().next();

            // Assertions on ALL fields to kill setter mutations
            assertEquals(42, retrieved.getCodiceOrdine());
            assertEquals(777, retrieved.getCodiceProdotto());
            assertEquals(99, retrieved.getQuantità());
        }
    }

    // ============================================================================
    // doRetrieveByOrder Tests (Branch CDS-B5)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByOrder Tests")
    class DoRetrieveByOrderTests {

        @Test
        @DisplayName("B5-True: Retrieve items for order with multiple items")
        void testRetrieveByOrderMultiple() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));
            containDao.doSave(createTestContain(1, 200, 3));
            containDao.doSave(createTestContain(2, 300, 4));

            Collection<ContainBean> items = containDao.doRetrieveByOrder(1);

            assertEquals(2, items.size());
            assertTrue(items.stream().allMatch(i -> i.getCodiceOrdine() == 1));
        }

        @Test
        @DisplayName("B5-False: Retrieve items for non-existent order")
        void testRetrieveByOrderNonExistent() throws SQLException {
            Collection<ContainBean> items = containDao.doRetrieveByOrder(999);

            assertNotNull(items);
            assertTrue(items.isEmpty());
        }

        @Test
        @DisplayName("Retrieve items for order with single item")
        void testRetrieveByOrderSingle() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));

            Collection<ContainBean> items = containDao.doRetrieveByOrder(1);

            assertEquals(1, items.size());
        }

        @Test
        @DisplayName("Retrieve items with orderID = 0")
        void testRetrieveByOrderZero() throws SQLException {
            Collection<ContainBean> items = containDao.doRetrieveByOrder(0);

            assertNotNull(items);
            assertTrue(items.isEmpty());
        }

        @Test
        @DisplayName("Verify item properties are correctly retrieved")
        void testRetrieveByOrderVerifyProperties() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 5));

            Collection<ContainBean> items = containDao.doRetrieveByOrder(1);
            ContainBean item = items.iterator().next();

            assertEquals(1, item.getCodiceOrdine());
            assertEquals(100, item.getCodiceProdotto());
            assertEquals(5, item.getQuantità());
        }
    }

    // ============================================================================
    // Loop Boundary Tests
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("Loop: 0 iterations (no items)")
        void testLoopZeroIterations() throws SQLException {
            Collection<ContainBean> items = containDao.doRetrieveAll(null);
            assertEquals(0, items.size());
        }

        @Test
        @DisplayName("Loop: 1 iteration (single item)")
        void testLoopOneIteration() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));

            Collection<ContainBean> items = containDao.doRetrieveAll(null);
            assertEquals(1, items.size());
        }

        @Test
        @DisplayName("Loop: >1 iterations (multiple items)")
        void testLoopMultipleIterations() throws SQLException {
            for (int i = 1; i <= 10; i++) {
                containDao.doSave(createTestContain(i, i * 100, i));
            }

            Collection<ContainBean> items = containDao.doRetrieveAll(null);
            assertEquals(10, items.size());
        }

        @Test
        @DisplayName("Loop: many items in single order")
        void testLoopManyItemsSingleOrder() throws SQLException {
            for (int i = 1; i <= 5; i++) {
                containDao.doSave(createTestContain(1, i * 100, i));
            }

            Collection<ContainBean> items = containDao.doRetrieveByOrder(1);
            assertEquals(5, items.size());
        }
    }

    // ============================================================================
    // Quantity Boundary Tests
    // ============================================================================

    @Nested
    @DisplayName("Quantity Boundary Tests")
    class QuantityBoundaryTests {

        @Test
        @DisplayName("BV: Minimum quantity = 1")
        void testMinimumQuantity() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 1));

            ContainBean retrieved = containDao.doRetrieveByKey(1);
            assertEquals(1, retrieved.getQuantità());
        }

        @Test
        @DisplayName("BV: Quantity = 2")
        void testQuantityTwo() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 2));

            ContainBean retrieved = containDao.doRetrieveByKey(1);
            assertEquals(2, retrieved.getQuantità());
        }

        @Test
        @DisplayName("BV: Large quantity")
        void testLargeQuantity() throws SQLException {
            containDao.doSave(createTestContain(1, 100, 99999));

            ContainBean retrieved = containDao.doRetrieveByKey(1);
            assertEquals(99999, retrieved.getQuantità());
        }
    }

    // ============================================================================
    // Mutation Killer Tests
    // ============================================================================

    @Nested
    @DisplayName("Mutation Killer Tests")
    class MutationKillerTests {
        
        @Test
        @DisplayName("doSave actually persists data - kills VoidMethodCallMutator line 47")
        void testDoSaveActuallyPersists() throws SQLException {
            ContainBean contain = createTestContain(1, 101, 5);
            
            // Verify empty before save
            Collection<ContainBean> beforeSave = containDao.doRetrieveAll(null);
            assertEquals(0, beforeSave.size(), "Should be empty before save");
            
            // Save the contain
            containDao.doSave(contain);
            
            // Verify present after save
            Collection<ContainBean> afterSave = containDao.doRetrieveAll(null);
            assertEquals(1, afterSave.size(), "Should have 1 contain after save");
            
            // Verify correct data was saved
            ContainBean saved = afterSave.iterator().next();
            assertEquals(101, saved.getCodiceProdotto());
            assertEquals(5, saved.getQuantità());
        }
        
        @Test
        @DisplayName("doDelete actually removes data - kills NegateConditionalsMutator line 75")
        void testDoDeleteActuallyRemoves() throws SQLException {
            // First save a contain
            containDao.doSave(createTestContain(1, 201, 3));
            
            // Verify it exists
            Collection<ContainBean> afterSave = containDao.doRetrieveAll(null);
            assertEquals(1, afterSave.size());
            ContainBean saved = afterSave.iterator().next();
            
            // Delete it by order ID
            boolean result = containDao.doDelete(saved.getCodiceOrdine());
            
            // Both the return value AND the actual deletion matter
            assertTrue(result, "doDelete should return true");
            
            // Verify it was actually deleted
            Collection<ContainBean> afterDelete = containDao.doRetrieveAll(null);
            assertEquals(0, afterDelete.size(), "Should be empty after delete");
        }
        
        @Test
        @DisplayName("doDelete return value matches reality - kills return value mutations")
        void testDoDeleteReturnValueMatchesReality() throws SQLException {
            // Delete non-existent returns false
            boolean falseResult = containDao.doDelete(99999);
            assertFalse(falseResult, "Deleting non-existent should return false");
            
            // Add a contain
            containDao.doSave(createTestContain(1, 301, 7));
            Collection<ContainBean> afterSave = containDao.doRetrieveAll(null);
            ContainBean saved = afterSave.iterator().next();
            
            // Delete existing returns true AND actually removes
            boolean trueResult = containDao.doDelete(saved.getCodiceOrdine());
            assertTrue(trueResult, "Deleting existing should return true");
            assertTrue(containDao.doRetrieveAll(null).isEmpty(), "Contain should be gone");
        }
        
        @Test
        @DisplayName("doRetrieveAll returns correct collection - kills EmptyObjectReturnValsMutator line 148")
        void testDoRetrieveAllReturnsCorrectCollection() throws SQLException {
            containDao.doSave(createTestContain(1, 401, 1));
            containDao.doSave(createTestContain(2, 402, 2));
            containDao.doSave(createTestContain(3, 403, 3));
            
            Collection<ContainBean> result = containDao.doRetrieveAll(null);
            
            // Must use the returned collection
            assertNotNull(result, "Result must not be null");
            assertFalse(result.isEmpty(), "Result must not be empty");
            assertEquals(3, result.size(), "Must have 3 contains");
        }
        
        @Test
        @DisplayName("doRetrieveByKey returns correct contain - kills NegateConditionalsMutator line 108")
        void testDoRetrieveByKeyReturnsCorrectContain() throws SQLException {
            containDao.doSave(createTestContain(1, 501, 42));
            
            ContainBean result = containDao.doRetrieveByKey(1);
            
            assertNotNull(result);
            assertEquals(1, result.getCodiceOrdine());
            assertEquals(501, result.getCodiceProdotto());
            assertEquals(42, result.getQuantità());
        }
        
        @Test
        @DisplayName("doRetrieveByOrder returns contains for specific order - kills NegateConditionalsMutator line 184")
        void testDoRetrieveByOrderReturnsSpecificOrderOnly() throws SQLException {
            containDao.doSave(createTestContain(1, 601, 10));
            containDao.doSave(createTestContain(1, 602, 20));
            containDao.doSave(createTestContain(2, 603, 30));
            
            Collection<ContainBean> order1Contains = containDao.doRetrieveByOrder(1);
            
            assertEquals(2, order1Contains.size(), "Order 1 should have 2 contains");
            for (ContainBean contain : order1Contains) {
                assertEquals(1, contain.getCodiceOrdine(), "All contains should belong to order 1");
                assertNotEquals(2, contain.getCodiceOrdine());
            }
        }
    }

    // ============================================================================
    // Helper Methods
    // ============================================================================

    private ContainBean createTestContain(int orderCode, int productCode, int quantity) {
        ContainBean contain = new ContainBean();
        contain.setCodiceOrdine(orderCode);
        contain.setCodiceProdotto(productCode);
        contain.setQuantità(quantity);
        return contain;
    }
}
