package model.bean;

import categories.UnitTest;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for UserBean.
 * 
 * Testing Level: Unit
 * Technique: Black-Box (Equivalence Class, Boundary Value) + Branch Coverage
 * 
 * ============================================================================
 * EQUIVALENCE CLASS DESIGN
 * ============================================================================
 * 
 * Field: username
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-USR-1     | Valid non-empty string     | "testuser"          | Yes    |
 * | EC-USR-2     | Empty string               | ""                  | Yes*   |
 * | EC-USR-3     | Null value                 | null                | Yes*   |
 * | EC-USR-4     | Single character           | "a"                 | Yes    |
 * | EC-USR-5     | Default value              | " "                 | Yes    |
 * -----------------------------------------------------------------
 * 
 * Field: user_admin
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-ADM-1     | Default value              | -1                  | Yes    |
 * | EC-ADM-2     | Non-admin                  | 0                   | Yes    |
 * | EC-ADM-3     | Admin                      | 1                   | Yes    |
 * | EC-ADM-4     | Invalid positive           | 2                   | Yes*   |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@UnitTest
@DisplayName("UserBean Unit Tests")
public class UserBeanTest {

    private UserBean userBean;

    @BeforeEach
    void setUp() {
        userBean = new UserBean();
    }

    // ============================================================================
    // Constructor Tests
    // ============================================================================

    @Nested
    @DisplayName("Constructor Tests")
    class ConstructorTests {

        @Test
        @DisplayName("Default constructor initializes with default values")
        void testDefaultConstructor() {
            UserBean bean = new UserBean();
            assertNotNull(bean);
            assertEquals(" ", bean.getUsername());
            assertEquals(" ", bean.getEmail());
            assertEquals(" ", bean.getPass());
            assertEquals(" ", bean.getNomeCognome());
            assertEquals(" ", bean.getSesso());
            assertEquals(" ", bean.getPaese());
            assertEquals(" ", bean.getDataNascita());
            assertEquals(-1, bean.getUserAdmin());
        }
    }

    // ============================================================================
    // Username Tests
    // ============================================================================

    @Nested
    @DisplayName("Username Tests")
    class UsernameTests {

        @Test
        @DisplayName("EC-USR-1: Set and get valid username")
        void testValidUsername() {
            userBean.setUsername("testuser");
            assertEquals("testuser", userBean.getUsername());
        }

        @Test
        @DisplayName("EC-USR-2: Set empty username")
        void testEmptyUsername() {
            userBean.setUsername("");
            assertEquals("", userBean.getUsername());
        }

        @Test
        @DisplayName("EC-USR-3: Set null username")
        void testNullUsername() {
            userBean.setUsername(null);
            assertNull(userBean.getUsername());
        }

        @Test
        @DisplayName("EC-USR-4: Set single character username")
        void testSingleCharUsername() {
            userBean.setUsername("a");
            assertEquals("a", userBean.getUsername());
        }

        @Test
        @DisplayName("EC-USR-5: Verify default username")
        void testDefaultUsername() {
            assertEquals(" ", userBean.getUsername());
        }

        @Test
        @DisplayName("BV: Long username")
        void testLongUsername() {
            String longUsername = "a".repeat(100);
            userBean.setUsername(longUsername);
            assertEquals(longUsername, userBean.getUsername());
        }
    }

    // ============================================================================
    // Email Tests
    // ============================================================================

    @Nested
    @DisplayName("Email Tests")
    class EmailTests {

        @Test
        @DisplayName("Set and get valid email")
        void testValidEmail() {
            userBean.setEmail("test@example.com");
            assertEquals("test@example.com", userBean.getEmail());
        }

        @Test
        @DisplayName("Set null email")
        void testNullEmail() {
            userBean.setEmail(null);
            assertNull(userBean.getEmail());
        }

        @Test
        @DisplayName("Set empty email")
        void testEmptyEmail() {
            userBean.setEmail("");
            assertEquals("", userBean.getEmail());
        }

        @Test
        @DisplayName("Verify default email")
        void testDefaultEmail() {
            assertEquals(" ", userBean.getEmail());
        }
    }

    // ============================================================================
    // Password Tests
    // ============================================================================

    @Nested
    @DisplayName("Password Tests")
    class PasswordTests {

        @Test
        @DisplayName("Set and get valid password")
        void testValidPassword() {
            userBean.setPass("securePass123");
            assertEquals("securePass123", userBean.getPass());
        }

        @Test
        @DisplayName("Set null password")
        void testNullPassword() {
            userBean.setPass(null);
            assertNull(userBean.getPass());
        }

        @Test
        @DisplayName("Set empty password")
        void testEmptyPassword() {
            userBean.setPass("");
            assertEquals("", userBean.getPass());
        }

        @Test
        @DisplayName("Verify default password")
        void testDefaultPassword() {
            assertEquals(" ", userBean.getPass());
        }
    }

    // ============================================================================
    // NomeCognome Tests
    // ============================================================================

    @Nested
    @DisplayName("NomeCognome Tests")
    class NomeCognomeTests {

        @Test
        @DisplayName("Set and get valid nome_cognome")
        void testValidNomeCognome() {
            userBean.setNomeCognome("John Doe");
            assertEquals("John Doe", userBean.getNomeCognome());
        }

        @Test
        @DisplayName("Set null nome_cognome")
        void testNullNomeCognome() {
            userBean.setNomeCognome(null);
            assertNull(userBean.getNomeCognome());
        }

        @Test
        @DisplayName("Verify default nome_cognome")
        void testDefaultNomeCognome() {
            assertEquals(" ", userBean.getNomeCognome());
        }
    }

    // ============================================================================
    // Sesso Tests
    // ============================================================================

    @Nested
    @DisplayName("Sesso Tests")
    class SessoTests {

        @Test
        @DisplayName("Set and get valid sesso")
        void testValidSesso() {
            userBean.setSesso("M");
            assertEquals("M", userBean.getSesso());
        }

        @Test
        @DisplayName("Set null sesso")
        void testNullSesso() {
            userBean.setSesso(null);
            assertNull(userBean.getSesso());
        }

        @Test
        @DisplayName("Verify default sesso")
        void testDefaultSesso() {
            assertEquals(" ", userBean.getSesso());
        }
    }

    // ============================================================================
    // Paese Tests
    // ============================================================================

    @Nested
    @DisplayName("Paese Tests")
    class PaeseTests {

        @Test
        @DisplayName("Set and get valid paese")
        void testValidPaese() {
            userBean.setPaese("Italy");
            assertEquals("Italy", userBean.getPaese());
        }

        @Test
        @DisplayName("Set null paese")
        void testNullPaese() {
            userBean.setPaese(null);
            assertNull(userBean.getPaese());
        }

        @Test
        @DisplayName("Verify default paese")
        void testDefaultPaese() {
            assertEquals(" ", userBean.getPaese());
        }
    }

    // ============================================================================
    // DataNascita Tests
    // ============================================================================

    @Nested
    @DisplayName("DataNascita Tests")
    class DataNascitaTests {

        @Test
        @DisplayName("Set and get valid data_nascita")
        void testValidDataNascita() {
            userBean.setDataNascita("1990-01-15");
            assertEquals("1990-01-15", userBean.getDataNascita());
        }

        @Test
        @DisplayName("Set null data_nascita")
        void testNullDataNascita() {
            userBean.setDataNascita(null);
            assertNull(userBean.getDataNascita());
        }

        @Test
        @DisplayName("Verify default data_nascita")
        void testDefaultDataNascita() {
            assertEquals(" ", userBean.getDataNascita());
        }
    }

    // ============================================================================
    // UserAdmin Tests
    // ============================================================================

    @Nested
    @DisplayName("UserAdmin Tests")
    class UserAdminTests {

        @Test
        @DisplayName("EC-ADM-1: Verify default admin value (-1)")
        void testDefaultAdmin() {
            assertEquals(-1, userBean.getUserAdmin());
        }

        @Test
        @DisplayName("EC-ADM-2: Set admin to 0 (non-admin)")
        void testNonAdmin() {
            userBean.setUserAdmin(0);
            assertEquals(0, userBean.getUserAdmin());
        }

        @Test
        @DisplayName("EC-ADM-3: Set admin to 1 (admin)")
        void testAdmin() {
            userBean.setUserAdmin(1);
            assertEquals(1, userBean.getUserAdmin());
        }

        @Test
        @DisplayName("EC-ADM-4: Set admin to 2 (invalid positive)")
        void testInvalidPositiveAdmin() {
            userBean.setUserAdmin(2);
            assertEquals(2, userBean.getUserAdmin());
        }

        @Test
        @DisplayName("BV: Negative admin value")
        void testNegativeAdmin() {
            userBean.setUserAdmin(-5);
            assertEquals(-5, userBean.getUserAdmin());
        }

        @Test
        @DisplayName("BV: Large admin value")
        void testLargeAdmin() {
            userBean.setUserAdmin(Integer.MAX_VALUE);
            assertEquals(Integer.MAX_VALUE, userBean.getUserAdmin());
        }
    }

    // ============================================================================
    // ToString Tests
    // ============================================================================

    @Nested
    @DisplayName("ToString Tests")
    class ToStringTests {

        @Test
        @DisplayName("toString returns username + user_admin")
        void testToString() {
            userBean.setUsername("testuser");
            userBean.setUserAdmin(1);
            assertEquals("testuser1", userBean.toString());
        }

        @Test
        @DisplayName("toString with default values")
        void testToStringDefaults() {
            assertEquals(" -1", userBean.toString());
        }

        @Test
        @DisplayName("toString with admin = 0")
        void testToStringNonAdmin() {
            userBean.setUsername("regular");
            userBean.setUserAdmin(0);
            assertEquals("regular0", userBean.toString());
        }
    }
}
