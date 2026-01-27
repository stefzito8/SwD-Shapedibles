package model.datasource;

import categories.IntegrationTest;
import integration.H2TestDatabase;
import model.bean.UserBean;
import org.junit.jupiter.api.*;

import javax.sql.DataSource;
import java.sql.SQLException;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Integration tests for UserDaoDataSource.
 * 
 * Testing Level: Integration
 * Technique: White-Box (Branch Coverage) with H2 Database
 * 
 * ============================================================================
 * BRANCH STRUCTURE
 * ============================================================================
 * 
 * Method: doRetrieveByKey(String username)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | UDS-B1    | rs.next()                    | Populate bean     | Return default |
 * -----------------------------------------------------------------
 * 
 * Method: doDelete(String username)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | UDS-B2    | result != 0                  | Return true       | Return false   |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveAll(String order)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | UDS-B3    | order != null && !order.equals("") | Add ORDER BY | No ORDER BY  |
 * | UDS-B4    | rs.next() loop               | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@IntegrationTest
@DisplayName("UserDaoDataSource Integration Tests")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public class UserDaoDataSourceTest {

    private static DataSource dataSource;
    private UserDaoDataSource userDao;

    @BeforeAll
    static void setUpClass() {
        dataSource = H2TestDatabase.getDataSource();
        H2TestDatabase.initializeDatabase();
    }

    @BeforeEach
    void setUp() {
        H2TestDatabase.resetDatabase();
        userDao = new UserDaoDataSource(dataSource);
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
        @DisplayName("Save new user successfully")
        void testSaveNewUser() throws SQLException {
            UserBean user = createTestUser("newuser", "new@example.com", "pass123", 0);

            userDao.doSave(user);

            UserBean retrieved = userDao.doRetrieveByKey("newuser");
            assertNotNull(retrieved);
            assertEquals("newuser", retrieved.getUsername());
            assertEquals("new@example.com", retrieved.getEmail());
        }

        @Test
        @DisplayName("Save admin user")
        void testSaveAdminUser() throws SQLException {
            UserBean admin = createTestUser("admin", "admin@example.com", "adminpass", 1);

            userDao.doSave(admin);

            UserBean retrieved = userDao.doRetrieveByKey("admin");
            assertEquals(1, retrieved.getUserAdmin());
        }

        @Test
        @DisplayName("Save user with all fields populated")
        void testSaveUserAllFields() throws SQLException {
            UserBean user = new UserBean();
            user.setUsername("fulluser");
            user.setEmail("full@example.com");
            user.setPass("password");
            user.setNomeCognome("John Doe");
            user.setSesso("M");
            user.setPaese("Italy");
            user.setDataNascita("1990-01-15");
            user.setUserAdmin(0);

            userDao.doSave(user);

            UserBean retrieved = userDao.doRetrieveByKey("fulluser");
            assertEquals("John Doe", retrieved.getNomeCognome());
            assertEquals("M", retrieved.getSesso());
            assertEquals("Italy", retrieved.getPaese());
        }

        @Test
        @DisplayName("Save duplicate user throws exception")
        void testSaveDuplicateUserThrowsException() throws SQLException {
            UserBean user1 = createTestUser("duplicate", "dup1@example.com", "pass1", 0);
            userDao.doSave(user1);

            UserBean user2 = createTestUser("duplicate", "dup2@example.com", "pass2", 0);

            assertThrows(SQLException.class, () -> userDao.doSave(user2));
        }
    }

    // ============================================================================
    // doRetrieveByKey Tests (Branch UDS-B1)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByKey Tests")
    class DoRetrieveByKeyTests {

        @Test
        @DisplayName("B1-True: Retrieve existing user populates bean")
        void testRetrieveExistingUser() throws SQLException {
            UserBean user = createTestUser("testuser", "test@example.com", "password", 0);
            userDao.doSave(user);

            UserBean retrieved = userDao.doRetrieveByKey("testuser");

            assertNotNull(retrieved);
            assertEquals("testuser", retrieved.getUsername());
            assertEquals("test@example.com", retrieved.getEmail());
        }

        @Test
        @DisplayName("B1-False: Retrieve non-existent user returns default bean")
        void testRetrieveNonExistentUser() throws SQLException {
            UserBean retrieved = userDao.doRetrieveByKey("nonexistent");
            
            // Returns a bean with default values (not null)
            assertNotNull(retrieved);
            assertEquals(" ", retrieved.getUsername()); // Default value
        }

        @Test
        @DisplayName("Retrieve user with empty username")
        void testRetrieveEmptyUsername() throws SQLException {
            UserBean retrieved = userDao.doRetrieveByKey("");
            
            assertNotNull(retrieved);
            assertEquals(" ", retrieved.getUsername()); // Default value
        }
    }

    // ============================================================================
    // doDelete Tests (Branch UDS-B2)
    // ============================================================================

    @Nested
    @DisplayName("doDelete Tests")
    class DoDeleteTests {

        @Test
        @DisplayName("B2-True: Delete existing user returns true")
        void testDeleteExistingUser() throws SQLException {
            UserBean user = createTestUser("deleteuser", "delete@example.com", "pass", 0);
            userDao.doSave(user);

            boolean result = userDao.doDelete("deleteuser");

            assertTrue(result);
            // Verify deletion
            UserBean retrieved = userDao.doRetrieveByKey("deleteuser");
            assertEquals(" ", retrieved.getUsername()); // Returns default bean
        }

        @Test
        @DisplayName("B2-False: Delete non-existent user returns false")
        void testDeleteNonExistentUser() throws SQLException {
            boolean result = userDao.doDelete("nonexistent");

            assertFalse(result);
        }

        @Test
        @DisplayName("Delete with empty username")
        void testDeleteEmptyUsername() throws SQLException {
            boolean result = userDao.doDelete("");

            assertFalse(result);
        }
    }

    // ============================================================================
    // doRetrieveAll Tests (Branches UDS-B3, UDS-B4)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveAll Tests")
    class DoRetrieveAllTests {

        @Test
        @DisplayName("B3-False, B4-False: Retrieve all from empty table")
        void testRetrieveAllEmpty() throws SQLException {
            Collection<UserBean> users = userDao.doRetrieveAll(null);

            assertNotNull(users);
            assertTrue(users.isEmpty());
        }

        @Test
        @DisplayName("B3-False, B4-True: Retrieve all without order")
        void testRetrieveAllWithoutOrder() throws SQLException {
            userDao.doSave(createTestUser("user1", "user1@example.com", "pass1", 0));
            userDao.doSave(createTestUser("user2", "user2@example.com", "pass2", 0));

            Collection<UserBean> users = userDao.doRetrieveAll(null);

            assertEquals(2, users.size());
        }

        @Test
        @DisplayName("B3-True, B4-True: Retrieve all with order by username")
        void testRetrieveAllWithOrder() throws SQLException {
            userDao.doSave(createTestUser("buser", "b@example.com", "pass", 0));
            userDao.doSave(createTestUser("auser", "a@example.com", "pass", 0));

            Collection<UserBean> users = userDao.doRetrieveAll("USERNAME");

            assertEquals(2, users.size());
            // First user should be 'auser' when ordered alphabetically
            UserBean first = users.iterator().next();
            assertEquals("auser", first.getUsername());
        }

        @Test
        @DisplayName("B3-False: Retrieve all with empty order string")
        void testRetrieveAllWithEmptyOrder() throws SQLException {
            userDao.doSave(createTestUser("user1", "user1@example.com", "pass1", 0));

            Collection<UserBean> users = userDao.doRetrieveAll("");

            assertEquals(1, users.size());
        }

        @Test
        @DisplayName("Retrieve all with multiple users")
        void testRetrieveAllMultipleUsers() throws SQLException {
            for (int i = 1; i <= 5; i++) {
                userDao.doSave(createTestUser("user" + i, "user" + i + "@example.com", "pass" + i, 0));
            }

            Collection<UserBean> users = userDao.doRetrieveAll(null);

            assertEquals(5, users.size());
        }

        @Test
        @DisplayName("Retrieve all with admin and non-admin users")
        void testRetrieveAllMixedUsers() throws SQLException {
            userDao.doSave(createTestUser("regular", "regular@example.com", "pass", 0));
            userDao.doSave(createTestUser("admin", "admin@example.com", "pass", 1));

            Collection<UserBean> users = userDao.doRetrieveAll(null);

            assertEquals(2, users.size());
            // Verify we have both admin and non-admin users
            boolean hasAdmin = users.stream().anyMatch(u -> u.getUserAdmin() == 1);
            boolean hasNonAdmin = users.stream().anyMatch(u -> u.getUserAdmin() == 0);
            assertTrue(hasAdmin);
            assertTrue(hasNonAdmin);
        }

        @Test
        @DisplayName("Verify all fields are populated in doRetrieveAll")
        void testRetrieveAllVerifiesAllFields() throws SQLException {
            UserBean user = new UserBean();
            user.setUsername("verifyuser");
            user.setEmail("verify@example.com");
            user.setPass("securepass123");
            user.setNomeCognome("Verify User Name");
            user.setSesso("F");
            user.setPaese("Germany");
            user.setDataNascita("1985-06-15");
            user.setUserAdmin(0);
            userDao.doSave(user);

            Collection<UserBean> users = userDao.doRetrieveAll(null);
            UserBean retrieved = users.iterator().next();

            // Assertions on ALL fields to kill setter mutations
            assertEquals("verifyuser", retrieved.getUsername());
            assertEquals("verify@example.com", retrieved.getEmail());
            assertEquals("securepass123", retrieved.getPass());
            assertEquals("Verify User Name", retrieved.getNomeCognome());
            assertEquals("F", retrieved.getSesso());
            assertEquals("Germany", retrieved.getPaese());
            assertEquals("1985-06-15", retrieved.getDataNascita());
            assertEquals(0, retrieved.getUserAdmin());
        }
    }

    // ============================================================================
    // Loop Boundary Tests
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("Loop: 0 iterations (no users)")
        void testLoopZeroIterations() throws SQLException {
            Collection<UserBean> users = userDao.doRetrieveAll(null);
            assertEquals(0, users.size());
        }

        @Test
        @DisplayName("Loop: 1 iteration (single user)")
        void testLoopOneIteration() throws SQLException {
            userDao.doSave(createTestUser("single", "single@example.com", "pass", 0));

            Collection<UserBean> users = userDao.doRetrieveAll(null);
            assertEquals(1, users.size());
        }

        @Test
        @DisplayName("Loop: >1 iterations (multiple users)")
        void testLoopMultipleIterations() throws SQLException {
            for (int i = 1; i <= 10; i++) {
                userDao.doSave(createTestUser("user" + i, "user" + i + "@example.com", "pass", 0));
            }

            Collection<UserBean> users = userDao.doRetrieveAll(null);
            assertEquals(10, users.size());
        }
    }

    // ============================================================================
    // Mutation Killer Tests
    // ============================================================================

    @Nested
    @DisplayName("Mutation Killer Tests")
    class MutationKillerTests {
        
        @Test
        @DisplayName("doSave actually persists data - kills VoidMethodCallMutator line 53")
        void testDoSaveActuallyPersists() throws SQLException {
            UserBean user = createTestUser("mutuser", "mut@test.com", "mutpass", 0);
            
            // Verify empty before save
            Collection<UserBean> beforeSave = userDao.doRetrieveAll(null);
            assertEquals(0, beforeSave.size(), "Should be empty before save");
            
            // Save the user
            userDao.doSave(user);
            
            // Verify present after save
            Collection<UserBean> afterSave = userDao.doRetrieveAll(null);
            assertEquals(1, afterSave.size(), "Should have 1 user after save");
            
            // Verify correct data was saved
            UserBean saved = userDao.doRetrieveByKey("mutuser");
            assertEquals("mutuser", saved.getUsername());
            assertEquals("mut@test.com", saved.getEmail());
        }
        
        @Test
        @DisplayName("doDelete actually removes data - kills NegateConditionalsMutator line 82")
        void testDoDeleteActuallyRemoves() throws SQLException {
            // First save a user
            userDao.doSave(createTestUser("deluser", "del@test.com", "delpass", 0));
            
            // Verify it exists
            UserBean beforeDelete = userDao.doRetrieveByKey("deluser");
            assertEquals("deluser", beforeDelete.getUsername());
            
            // Delete it
            boolean result = userDao.doDelete("deluser");
            
            // Both the return value AND the actual deletion matter
            assertTrue(result, "doDelete should return true");
            
            // Verify it was actually deleted
            Collection<UserBean> afterDelete = userDao.doRetrieveAll(null);
            assertEquals(0, afterDelete.size(), "Should be empty after delete");
        }
        
        @Test
        @DisplayName("doDelete return value matches reality - kills return value mutations")
        void testDoDeleteReturnValueMatchesReality() throws SQLException {
            // Delete non-existent returns false
            boolean falseResult = userDao.doDelete("nonexistent");
            assertFalse(falseResult, "Deleting non-existent should return false");
            
            // Add a user
            userDao.doSave(createTestUser("retuser", "ret@test.com", "retpass", 0));
            
            // Delete existing returns true AND actually removes
            boolean trueResult = userDao.doDelete("retuser");
            assertTrue(trueResult, "Deleting existing should return true");
            assertTrue(userDao.doRetrieveAll(null).isEmpty(), "User should be gone");
        }
        
        @Test
        @DisplayName("doRetrieveAll returns correct collection - kills EmptyObjectReturnValsMutator line 166")
        void testDoRetrieveAllReturnsCorrectCollection() throws SQLException {
            userDao.doSave(createTestUser("user1", "u1@test.com", "pass1", 0));
            userDao.doSave(createTestUser("user2", "u2@test.com", "pass2", 0));
            userDao.doSave(createTestUser("user3", "u3@test.com", "pass3", 1));
            
            Collection<UserBean> result = userDao.doRetrieveAll(null);
            
            // Must use the returned collection
            assertNotNull(result, "Result must not be null");
            assertFalse(result.isEmpty(), "Result must not be empty");
            assertEquals(3, result.size(), "Must have 3 users");
        }
        
        @Test
        @DisplayName("doRetrieveByKey returns correct user - kills NegateConditionalsMutator line 121")
        void testDoRetrieveByKeyReturnsCorrectUser() throws SQLException {
            userDao.doSave(createTestUser("keyuser", "key@test.com", "keypass", 0));
            
            UserBean result = userDao.doRetrieveByKey("keyuser");
            
            assertNotNull(result);
            assertEquals("keyuser", result.getUsername());
            assertEquals("key@test.com", result.getEmail());
            assertEquals("Test User", result.getNomeCognome());
            assertEquals("M", result.getSesso());
            assertEquals("Italy", result.getPaese());
            assertEquals(0, result.getUserAdmin());
        }
        
        @Test
        @DisplayName("Admin flag is correctly saved and retrieved - kills boundary mutations")
        void testAdminFlagCorrectlySavedAndRetrieved() throws SQLException {
            // Non-admin user
            userDao.doSave(createTestUser("normaluser", "normal@test.com", "pass", 0));
            UserBean normal = userDao.doRetrieveByKey("normaluser");
            assertEquals(0, normal.getUserAdmin());
            assertNotEquals(1, normal.getUserAdmin());
            
            // Admin user
            userDao.doSave(createTestUser("adminuser", "admin@test.com", "pass", 1));
            UserBean admin = userDao.doRetrieveByKey("adminuser");
            assertEquals(1, admin.getUserAdmin());
            assertNotEquals(0, admin.getUserAdmin());
        }
    }

    // ============================================================================
    // Helper Methods
    // ============================================================================

    private UserBean createTestUser(String username, String email, String password, int admin) {
        UserBean user = new UserBean();
        user.setUsername(username);
        user.setEmail(email);
        user.setPass(password);
        user.setNomeCognome("Test User");
        user.setSesso("M");
        user.setPaese("Italy");
        user.setDataNascita("1990-01-01");
        user.setUserAdmin(admin);
        return user;
    }
}
