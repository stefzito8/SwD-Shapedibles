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

        @Test
        @DisplayName("Verify all fields are populated in doRetrieveAll")
        void testRetrieveAllVerifiesAllFields() throws SQLException {
            addressDao.doSave(createTestAddress("addr1", "testuser", "Germany", "Hauptstrasse", "Berlin", 123, "10115"));

            Collection<AddressBean> addresses = addressDao.doRetrieveAll(null);
            AddressBean retrieved = addresses.iterator().next();

            // Assertions on ALL fields to kill setter mutations
            assertEquals("addr1", retrieved.getId());
            assertEquals("testuser", retrieved.getUtente());
            assertEquals("Germany", retrieved.getPaese());
            assertEquals("Hauptstrasse", retrieved.getStrada());
            assertEquals("Berlin", retrieved.getCittà());
            assertEquals(123, retrieved.getNumero());
            assertEquals("10115", retrieved.getCodicePostale());
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

        @Test
        @DisplayName("Verify all fields are populated in doRetrieveByUser")
        void testRetrieveByUserVerifiesAllFields() throws SQLException {
            addressDao.doSave(createTestAddress("addr2", "verifyuser", "France", "Rue de Paris", "Lyon", 456, "69001"));

            Collection<AddressBean> addresses = addressDao.doRetrieveByUser("verifyuser");
            AddressBean retrieved = addresses.iterator().next();

            // Assertions on ALL fields to kill setter mutations
            assertEquals("addr2", retrieved.getId());
            assertEquals("verifyuser", retrieved.getUtente());
            assertEquals("France", retrieved.getPaese());
            assertEquals("Rue de Paris", retrieved.getStrada());
            assertEquals("Lyon", retrieved.getCittà());
            assertEquals(456, retrieved.getNumero());
            assertEquals("69001", retrieved.getCodicePostale());
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
    // Mutation Killer Tests
    // ============================================================================

    @Nested
    @DisplayName("Mutation Killer Tests")
    class MutationKillerTests {
        
        @Test
        @DisplayName("doSave actually persists data - kills VoidMethodCallMutator line 49")
        void testDoSaveActuallyPersists() throws SQLException {
            AddressBean address = createTestAddress("mut1", "mutuser", "Germany", "Musterstr", "Berlin", 123, "10115");
            
            // Verify empty before save
            Collection<AddressBean> beforeSave = addressDao.doRetrieveAll(null);
            assertEquals(0, beforeSave.size(), "Should be empty before save");
            
            // Save the address
            addressDao.doSave(address);
            
            // Verify present after save
            Collection<AddressBean> afterSave = addressDao.doRetrieveAll(null);
            assertEquals(1, afterSave.size(), "Should have 1 address after save");
            
            // Verify correct data was saved
            AddressBean saved = addressDao.doRetrieveByKey("mut1", "mutuser");
            assertEquals("mut1", saved.getId());
            assertEquals("mutuser", saved.getUtente());
            assertEquals("Germany", saved.getPaese());
        }
        
        @Test
        @DisplayName("doDelete actually removes data - kills NegateConditionalsMutator line 77")
        void testDoDeleteActuallyRemoves() throws SQLException {
            // First save an address
            addressDao.doSave(createTestAddress("del1", "deluser", "Spain", "Calle Mayor", "Madrid", 1, "28001"));
            
            // Verify it exists
            AddressBean beforeDelete = addressDao.doRetrieveByKey("del1", "deluser");
            assertEquals("del1", beforeDelete.getId());
            
            // Delete it
            boolean result = addressDao.doDelete("del1", "deluser");
            
            // Both the return value AND the actual deletion matter
            assertTrue(result, "doDelete should return true");
            
            // Verify it was actually deleted
            Collection<AddressBean> afterDelete = addressDao.doRetrieveAll(null);
            assertEquals(0, afterDelete.size(), "Should be empty after delete");
        }
        
        @Test
        @DisplayName("doDelete return value matches reality - kills return value mutations")
        void testDoDeleteReturnValueMatchesReality() throws SQLException {
            // Delete non-existent returns false
            boolean falseResult = addressDao.doDelete("nonexistent", "nouser");
            assertFalse(falseResult, "Deleting non-existent should return false");
            
            // Add an address
            addressDao.doSave(createTestAddress("ret1", "retuser", "UK", "Baker St", "London", 221, "NW1 6XE"));
            
            // Delete existing returns true AND actually removes
            boolean trueResult = addressDao.doDelete("ret1", "retuser");
            assertTrue(trueResult, "Deleting existing should return true");
            assertTrue(addressDao.doRetrieveAll(null).isEmpty(), "Address should be gone");
        }
        
        @Test
        @DisplayName("doRetrieveAll returns correct collection - kills EmptyObjectReturnValsMutator line 160")
        void testDoRetrieveAllReturnsCorrectCollection() throws SQLException {
            addressDao.doSave(createTestAddress("a1", "user1", "Italy", "Via Roma", "Rome", 1, "00100"));
            addressDao.doSave(createTestAddress("a2", "user2", "France", "Rue Paris", "Paris", 2, "75001"));
            addressDao.doSave(createTestAddress("a3", "user3", "Spain", "Calle Sol", "Madrid", 3, "28001"));
            
            Collection<AddressBean> result = addressDao.doRetrieveAll(null);
            
            // Must use the returned collection
            assertNotNull(result, "Result must not be null");
            assertFalse(result.isEmpty(), "Result must not be empty");
            assertEquals(3, result.size(), "Must have 3 addresses");
        }
        
        @Test
        @DisplayName("doRetrieveByKey returns correct address - kills NegateConditionalsMutator line 116")
        void testDoRetrieveByKeyReturnsCorrectAddress() throws SQLException {
            addressDao.doSave(createTestAddress("key1", "keyuser", "Portugal", "Rua Lisboa", "Lisboa", 99, "1100-001"));
            
            AddressBean result = addressDao.doRetrieveByKey("key1", "keyuser");
            
            assertNotNull(result);
            assertEquals("key1", result.getId());
            assertEquals("keyuser", result.getUtente());
            assertEquals("Portugal", result.getPaese());
            assertEquals("Rua Lisboa", result.getStrada());
            assertEquals("Lisboa", result.getCittà());
            assertEquals(99, result.getNumero());
            assertEquals("1100-001", result.getCodicePostale());
        }
        
        @Test
        @DisplayName("doRetrieveByUser returns addresses for specific user - kills NegateConditionalsMutator line 201")
        void testDoRetrieveByUserReturnsSpecificUserOnly() throws SQLException {
            addressDao.doSave(createTestAddress("u1a1", "user1", "Italy", "Street1", "City1", 1, "11111"));
            addressDao.doSave(createTestAddress("u1a2", "user1", "France", "Street2", "City2", 2, "22222"));
            addressDao.doSave(createTestAddress("u2a1", "user2", "Spain", "Street3", "City3", 3, "33333"));
            
            Collection<AddressBean> user1Addresses = addressDao.doRetrieveByUser("user1");
            
            assertEquals(2, user1Addresses.size(), "User1 should have 2 addresses");
            for (AddressBean addr : user1Addresses) {
                assertEquals("user1", addr.getUtente(), "All addresses should belong to user1");
                assertNotEquals("user2", addr.getUtente());
            }
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
