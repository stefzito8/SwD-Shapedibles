package model.datasource;

import categories.IntegrationTest;
import integration.H2TestDatabase;
import model.bean.AddressBean;
import org.junit.jupiter.api.*;

import javax.sql.DataSource;
import java.sql.SQLException;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Integration tests for AddressDaoDataSource.
 * 
 * Testing Level: Integration
 * Technique: White-Box (Branch Coverage) with H2 Database
 * 
 * ============================================================================
 * BRANCH STRUCTURE
 * ============================================================================
 * 
 * Method: doRetrieveByKey(String id, String user)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | ADS-B1    | rs.next()                    | Populate bean     | Return default |
 * -----------------------------------------------------------------
 * 
 * Method: doDelete(String id, String user)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | ADS-B2    | result != 0                  | Return true       | Return false   |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveAll(String order)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | ADS-B3    | order != null && !order.equals("") | Add ORDER BY | No ORDER BY  |
 * | ADS-B4    | rs.next() loop               | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveByUser(String user)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | ADS-B5    | rs.next() loop               | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@IntegrationTest
@DisplayName("AddressDaoDataSource Integration Tests")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public class AddressDaoDataSourceTest {

    private static DataSource dataSource;
    private AddressDaoDataSource addressDao;

    @BeforeAll
    static void setUpClass() {
        dataSource = H2TestDatabase.getDataSource();
        H2TestDatabase.initializeDatabase();
    }

    @BeforeEach
    void setUp() {
        H2TestDatabase.resetDatabase();
        addressDao = new AddressDaoDataSource(dataSource);
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
        @DisplayName("Save new address successfully")
        void testSaveNewAddress() throws SQLException {
            AddressBean address = createTestAddress("1", "user1", "Italy", "Via Roma", "Rome", 42, "00100");

            addressDao.doSave(address);

            AddressBean retrieved = addressDao.doRetrieveByKey("1", "user1");
            assertNotNull(retrieved);
            assertEquals("1", retrieved.getId());
            assertEquals("user1", retrieved.getUtente());
            assertEquals("Via Roma", retrieved.getStrada());
        }

        @Test
        @DisplayName("Save address with all fields")
        void testSaveAddressAllFields() throws SQLException {
            AddressBean address = createTestAddress("2", "user2", "USA", "Main Street", "New York", 100, "10001");

            addressDao.doSave(address);

            AddressBean retrieved = addressDao.doRetrieveByKey("2", "user2");
            assertEquals("USA", retrieved.getPaese());
            assertEquals("Main Street", retrieved.getStrada());
            assertEquals("New York", retrieved.getCittà());
            assertEquals(100, retrieved.getNumero());
            assertEquals("10001", retrieved.getCodicePostale());
        }

        @Test
        @DisplayName("Save multiple addresses for same user")
        void testSaveMultipleAddressesSameUser() throws SQLException {
            addressDao.doSave(createTestAddress("home", "user1", "Italy", "Home St", "Rome", 1, "00100"));
            addressDao.doSave(createTestAddress("work", "user1", "Italy", "Work St", "Rome", 2, "00200"));

            Collection<AddressBean> addresses = addressDao.doRetrieveByUser("user1");
            assertEquals(2, addresses.size());
        }
    }

    // ============================================================================
    // doRetrieveByKey Tests (Branch ADS-B1)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByKey Tests")
    class DoRetrieveByKeyTests {

        @Test
        @DisplayName("B1-True: Retrieve existing address populates bean")
        void testRetrieveExistingAddress() throws SQLException {
            addressDao.doSave(createTestAddress("1", "user1", "Italy", "Via Roma", "Rome", 42, "00100"));

            AddressBean retrieved = addressDao.doRetrieveByKey("1", "user1");

            assertNotNull(retrieved);
            assertEquals("1", retrieved.getId());
            assertEquals("user1", retrieved.getUtente());
            assertEquals("Italy", retrieved.getPaese());
        }

        @Test
        @DisplayName("B1-False: Retrieve non-existent address returns default bean")
        void testRetrieveNonExistentAddress() throws SQLException {
            AddressBean retrieved = addressDao.doRetrieveByKey("999", "nonexistent");

            assertNotNull(retrieved);
            assertNull(retrieved.getId()); // Default bean has null id
        }

        @Test
        @DisplayName("Retrieve with wrong user returns default bean")
        void testRetrieveWrongUser() throws SQLException {
            addressDao.doSave(createTestAddress("1", "user1", "Italy", "Via Roma", "Rome", 42, "00100"));

            AddressBean retrieved = addressDao.doRetrieveByKey("1", "wronguser");

            assertNotNull(retrieved);
            assertNull(retrieved.getId());
        }

        @Test
        @DisplayName("Retrieve with wrong id returns default bean")
        void testRetrieveWrongId() throws SQLException {
            addressDao.doSave(createTestAddress("1", "user1", "Italy", "Via Roma", "Rome", 42, "00100"));

            AddressBean retrieved = addressDao.doRetrieveByKey("wrongid", "user1");

            assertNotNull(retrieved);
            assertNull(retrieved.getId());
        }
    }

    // ============================================================================
    // doDelete Tests (Branch ADS-B2)
    // ============================================================================

    @Nested
    @DisplayName("doDelete Tests")
    class DoDeleteTests {

        @Test
        @DisplayName("B2-True: Delete existing address returns true")
        void testDeleteExistingAddress() throws SQLException {
            addressDao.doSave(createTestAddress("1", "user1", "Italy", "Via Roma", "Rome", 42, "00100"));

            boolean result = addressDao.doDelete("1", "user1");

            assertTrue(result);
            // Verify deletion
            AddressBean retrieved = addressDao.doRetrieveByKey("1", "user1");
            assertNull(retrieved.getId());
        }

        @Test
        @DisplayName("B2-False: Delete non-existent address returns false")
        void testDeleteNonExistentAddress() throws SQLException {
            boolean result = addressDao.doDelete("999", "nonexistent");

            assertFalse(result);
        }

        @Test
        @DisplayName("Delete with wrong user returns false")
        void testDeleteWrongUser() throws SQLException {
            addressDao.doSave(createTestAddress("1", "user1", "Italy", "Via Roma", "Rome", 42, "00100"));

            boolean result = addressDao.doDelete("1", "wronguser");

            assertFalse(result);
            // Original address should still exist
            AddressBean retrieved = addressDao.doRetrieveByKey("1", "user1");
            assertEquals("1", retrieved.getId());
        }
    }

    // ============================================================================
    // doRetrieveAll Tests (Branches ADS-B3, ADS-B4)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveAll Tests")
    class DoRetrieveAllTests {

        @Test
        @DisplayName("B3-False, B4-False: Retrieve all from empty table")
        void testRetrieveAllEmpty() throws SQLException {
            Collection<AddressBean> addresses = addressDao.doRetrieveAll(null);

            assertNotNull(addresses);
            assertTrue(addresses.isEmpty());
        }

        @Test
        @DisplayName("B3-False, B4-True: Retrieve all without order")
        void testRetrieveAllWithoutOrder() throws SQLException {
            addressDao.doSave(createTestAddress("1", "user1", "Italy", "Via A", "Rome", 1, "00100"));
            addressDao.doSave(createTestAddress("2", "user2", "USA", "Street B", "NYC", 2, "10001"));

            Collection<AddressBean> addresses = addressDao.doRetrieveAll(null);

            assertEquals(2, addresses.size());
        }

        @Test
        @DisplayName("B3-True, B4-True: Retrieve all with order")
        void testRetrieveAllWithOrder() throws SQLException {
            addressDao.doSave(createTestAddress("2", "user2", "USA", "Street B", "NYC", 2, "10001"));
            addressDao.doSave(createTestAddress("1", "user1", "Italy", "Via A", "Rome", 1, "00100"));

            Collection<AddressBean> addresses = addressDao.doRetrieveAll("ID");

            assertEquals(2, addresses.size());
            // First address should have ID "1" when ordered
            AddressBean first = addresses.iterator().next();
            assertEquals("1", first.getId());
        }

        @Test
        @DisplayName("B3-False: Retrieve all with empty order string")
        void testRetrieveAllEmptyOrder() throws SQLException {
            addressDao.doSave(createTestAddress("1", "user1", "Italy", "Via A", "Rome", 1, "00100"));

            Collection<AddressBean> addresses = addressDao.doRetrieveAll("");

            assertEquals(1, addresses.size());
        }
    }

    // ============================================================================
    // doRetrieveByUser Tests (Branch ADS-B5)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByUser Tests")
    class DoRetrieveByUserTests {

        @Test
        @DisplayName("B5-True: Retrieve addresses for user with multiple addresses")
        void testRetrieveByUserMultiple() throws SQLException {
            addressDao.doSave(createTestAddress("home", "user1", "Italy", "Home St", "Rome", 1, "00100"));
            addressDao.doSave(createTestAddress("work", "user1", "Italy", "Work St", "Rome", 2, "00200"));
            addressDao.doSave(createTestAddress("other", "user2", "Italy", "Other St", "Milan", 3, "00300"));

            Collection<AddressBean> addresses = addressDao.doRetrieveByUser("user1");

            assertEquals(2, addresses.size());
            assertTrue(addresses.stream().allMatch(a -> "user1".equals(a.getUtente())));
        }

        @Test
        @DisplayName("B5-False: Retrieve addresses for non-existent user")
        void testRetrieveByUserNonExistent() throws SQLException {
            Collection<AddressBean> addresses = addressDao.doRetrieveByUser("nonexistent");

            assertNotNull(addresses);
            assertTrue(addresses.isEmpty());
        }

        @Test
        @DisplayName("Retrieve addresses for user with single address")
        void testRetrieveByUserSingle() throws SQLException {
            addressDao.doSave(createTestAddress("1", "singleuser", "Italy", "Via Roma", "Rome", 1, "00100"));

            Collection<AddressBean> addresses = addressDao.doRetrieveByUser("singleuser");

            assertEquals(1, addresses.size());
        }

        @Test
        @DisplayName("Retrieve addresses with empty username")
        void testRetrieveByUserEmpty() throws SQLException {
            Collection<AddressBean> addresses = addressDao.doRetrieveByUser("");

            assertNotNull(addresses);
            assertTrue(addresses.isEmpty());
        }
    }

    // ============================================================================
    // Loop Boundary Tests
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("Loop: 0 iterations (no addresses)")
        void testLoopZeroIterations() throws SQLException {
            Collection<AddressBean> addresses = addressDao.doRetrieveAll(null);
            assertEquals(0, addresses.size());
        }

        @Test
        @DisplayName("Loop: 1 iteration (single address)")
        void testLoopOneIteration() throws SQLException {
            addressDao.doSave(createTestAddress("1", "user1", "Italy", "Via Roma", "Rome", 1, "00100"));

            Collection<AddressBean> addresses = addressDao.doRetrieveAll(null);
            assertEquals(1, addresses.size());
        }

        @Test
        @DisplayName("Loop: >1 iterations (multiple addresses)")
        void testLoopMultipleIterations() throws SQLException {
            for (int i = 1; i <= 5; i++) {
                addressDao.doSave(createTestAddress(String.valueOf(i), "user" + i, "Country" + i, 
                    "Street" + i, "City" + i, i, "0000" + i));
            }

            Collection<AddressBean> addresses = addressDao.doRetrieveAll(null);
            assertEquals(5, addresses.size());
        }
    }

    // ============================================================================
    // Helper Methods
    // ============================================================================

    private AddressBean createTestAddress(String id, String user, String country, String street, 
                                          String city, int number, String postalCode) {
        AddressBean address = new AddressBean();
        address.setId(id);
        address.setUtente(user);
        address.setPaese(country);
        address.setStrada(street);
        address.setCittà(city);
        address.setNumero(number);
        address.setCodicePostale(postalCode);
        return address;
    }
}
