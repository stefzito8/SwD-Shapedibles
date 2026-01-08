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
