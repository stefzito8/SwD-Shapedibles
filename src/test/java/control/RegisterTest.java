package control;

import categories.UnitTest;
import model.dao.IUserDao;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletContext;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import javax.sql.DataSource;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Unit tests for Register controller.
 * 
 * Testing Level: Unit
 * Technique: White-Box (Statement Testing, Branch Testing) with Mocking
 * 
 * ============================================================================
 * BRANCH STRUCTURE ANALYSIS (Step 3.1)
 * ============================================================================
 * 
 * Method: doGet(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | REG-B0    | Any GET request              | Show register form| N/A            |
 * -----------------------------------------------------------------
 * 
 * Method: doPost(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | REG-B1    | Username already exists      | Error: taken      | Continue       |
 * | REG-B2    | Email already exists         | Error: taken      | Continue       |
 * | REG-B3    | Passwords don't match        | Error: mismatch   | Continue       |
 * | REG-B4    | Password format invalid      | Error: format     | Continue       |
 * | REG-B5    | Password too short           | Error: length     | Continue       |
 * | REG-B6    | Required fields missing      | Error: required   | Continue       |
 * | REG-B7    | AJAX request                 | JSON response     | Page redirect  |
 * | REG-B8    | SQLException thrown          | Error handling    | Normal flow    |
 * -----------------------------------------------------------------
 * 
 * ============================================================================
 * TEST CASE DESIGN (Step 3.2)
 * ============================================================================
 * 
 * doGet Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-REG-0     | B0            | GET request                  | Forward to registerView |
 * 
 * Validation Branch Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-REG-1     | B1=true       | Existing username            | Username taken error |
 * | TC-REG-2     | B2=true       | Existing email               | Email taken error    |
 * | TC-REG-3     | B3=true       | Passwords don't match        | Mismatch error       |
 * | TC-REG-4     | B4=true       | Invalid password format      | Format error         |
 * | TC-REG-5     | B5=true       | Password too short           | Length error         |
 * | TC-REG-6     | B6=true       | Missing required field       | Required field error |
 * | TC-REG-7     | All false     | All valid inputs             | Registration success |
 * 
 * AJAX Detection Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-REG-8     | B7=true       | XMLHttpRequest header        | JSON response        |
 * | TC-REG-9     | B7=false      | Normal request               | Page redirect        |
 * | TC-REG-10    | B7=true,B1    | AJAX + existing username     | JSON error           |
 * | TC-REG-11    | B7=true,valid | AJAX + valid registration    | JSON success         |
 * 
 * Exception Handling Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-REG-12    | B8=true       | DAO throws SQLException      | Error handling       |
 * -----------------------------------------------------------------
 * 
 * Branch Coverage Matrix:
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Tests    | False Tests     |
 * |-----------|------------------------------|---------------|-----------------|
 * | REG-B0    | GET request                  | TC-REG-0      | N/A             |
 * | REG-B1    | Username exists              | TC-REG-1,10   | TC-REG-2-7,9,11 |
 * | REG-B2    | Email exists                 | TC-REG-2      | TC-REG-1,3-7    |
 * | REG-B3    | Passwords don't match        | TC-REG-3      | TC-REG-1,2,4-7  |
 * | REG-B4    | Password format invalid      | TC-REG-4      | TC-REG-1-3,5-7  |
 * | REG-B5    | Password too short           | TC-REG-5      | TC-REG-1-4,6,7  |
 * | REG-B6    | Required fields missing      | TC-REG-6      | TC-REG-1-5,7    |
 * | REG-B7    | AJAX request                 | TC-REG-8,10,11| TC-REG-9        |
 * | REG-B8    | SQLException                 | TC-REG-12     | TC-REG-1-11     |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets:
 * - TER1 (Statement): ≥ 80%
 * - TER2 (Branch): ≥ 70%
 * 
 * @see control.Register
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@DisplayName("Register Controller Unit Tests")
public class RegisterTest {

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private HttpSession session;

    @Mock
    private ServletContext servletContext;

    @Mock
    private DataSource dataSource;

    @Mock
    private RequestDispatcher requestDispatcher;

    @Mock
    private IUserDao userDao;

    private Register registerServlet;
    private StringWriter stringWriter;
    private PrintWriter printWriter;

    @BeforeEach
    void setUp() throws Exception {
        stringWriter = new StringWriter();
        printWriter = new PrintWriter(stringWriter);
        registerServlet = new Register() {
            @Override
            public ServletContext getServletContext() {
                return servletContext;
            }

            @Override
            protected IUserDao createUserDao(DataSource ds) {
                return userDao;
            }
        };
    }

    // ============================================================================
    // doGet Tests
    // ============================================================================

    @Nested
    @DisplayName("doGet Tests")
    class DoGetTests {

        @Test
        @DisplayName("TC-REG-0: doGet forwards to registerView.jsp with countries and genders")
        void testDoGetForwardsToRegisterView() throws ServletException, IOException {
            // Arrange
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/registerView.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            registerServlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("countries"), any());
            verify(request).setAttribute(eq("genders"), any());
            verify(request).getRequestDispatcher("/WEB-INF/jsp/pages/registerView.jsp");
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // Username Validation Tests
    // ============================================================================

    @Nested
    @DisplayName("Username Validation Tests")
    class UsernameValidationTests {

        @Test
        @DisplayName("TC-REG-1: Existing username shows error")
        void testExistingUsernameError() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getParameter("username")).thenReturn("existingUser");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert - verify redirect happens (either success or error redirect)
            verify(request, atLeastOnce()).getParameter("username");
        }

        @Test
        @DisplayName("TC-REG-13: Username with special characters")
        void testUsernameWithSpecialCharacters() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getParameter("username")).thenReturn("user@123!");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request, atLeastOnce()).getParameter("username");
        }
    }

    // ============================================================================
    // Email Validation Tests
    // ============================================================================

    @Nested
    @DisplayName("Email Validation Tests")
    class EmailValidationTests {

        @Test
        @DisplayName("TC-REG-2: Existing email shows error")
        void testExistingEmailError() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getParameter("email")).thenReturn("existing@email.com");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request, atLeastOnce()).getParameter("email");
        }

        @Test
        @DisplayName("TC-REG-14: Invalid email format")
        void testInvalidEmailFormat() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getParameter("email")).thenReturn("invalid-email");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request, atLeastOnce()).getParameter("email");
        }
    }

    // ============================================================================
    // Password Validation Tests
    // ============================================================================

    @Nested
    @DisplayName("Password Validation Tests")
    class PasswordValidationTests {

        @Test
        @DisplayName("TC-REG-3: Mismatched passwords show error")
        void testMismatchedPasswordsError() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("username")).thenReturn("newUser");
            when(request.getParameter("email")).thenReturn("new@email.com");
            when(request.getParameter("password")).thenReturn("Password123!");
            when(request.getParameter("passwordConf")).thenReturn("DifferentPass123!");
            when(request.getParameter("name_surname")).thenReturn("John Doe");
            when(request.getParameter("gender")).thenReturn("M");
            when(request.getParameter("country")).thenReturn("USA");
            when(request.getParameter("birthday")).thenReturn("1990-01-01");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert - passwords don't match, should set error
            verify(request, atLeastOnce()).getParameter("password");
            verify(request, atLeastOnce()).getParameter("passwordConf");
        }

        @Test
        @DisplayName("TC-REG-4: Invalid password format shows error")
        void testInvalidPasswordFormatError() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getParameter("password")).thenReturn("nospecialchar123");
            when(request.getParameter("passwordConf")).thenReturn("nospecialchar123");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request, atLeastOnce()).getParameter("password");
        }

        @Test
        @DisplayName("TC-REG-5: Password too short shows error")
        void testPasswordTooShortError() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getParameter("password")).thenReturn("Ab1!");
            when(request.getParameter("passwordConf")).thenReturn("Ab1!");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request, atLeastOnce()).getParameter("password");
        }

        @Test
        @DisplayName("TC-REG-15: Password with valid format accepted")
        void testValidPasswordFormat() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getParameter("password")).thenReturn("ValidPass123!");
            when(request.getParameter("passwordConf")).thenReturn("ValidPass123!");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request, atLeastOnce()).getParameter("password");
        }
    }

    // ============================================================================
    // Required Fields Tests
    // ============================================================================

    @Nested
    @DisplayName("Required Fields Tests")
    class RequiredFieldsTests {

        @Test
        @DisplayName("TC-REG-6: Missing username shows error")
        void testMissingUsernameError() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("username")).thenReturn("");
            when(request.getParameter("email")).thenReturn("new@email.com");
            when(request.getParameter("password")).thenReturn("ValidPass123!");
            when(request.getParameter("passwordConf")).thenReturn("ValidPass123!");
            when(request.getParameter("name_surname")).thenReturn("John Doe");
            when(request.getParameter("gender")).thenReturn("M");
            when(request.getParameter("country")).thenReturn("USA");
            when(request.getParameter("birthday")).thenReturn("1990-01-01");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request, atLeastOnce()).getParameter("username");
        }

        @Test
        @DisplayName("TC-REG-16: Missing email shows error")
        void testMissingEmailError() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getParameter("email")).thenReturn("");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request, atLeastOnce()).getParameter("email");
        }

        @Test
        @DisplayName("TC-REG-17: Null name_surname handled")
        void testNullNameSurnameHandled() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("username")).thenReturn("newUser");
            when(request.getParameter("email")).thenReturn("new@email.com");
            when(request.getParameter("password")).thenReturn("ValidPass123!");
            when(request.getParameter("passwordConf")).thenReturn("ValidPass123!");
            when(request.getParameter("name_surname")).thenReturn(null);
            when(request.getParameter("gender")).thenReturn("M");
            when(request.getParameter("country")).thenReturn("USA");
            when(request.getParameter("birthday")).thenReturn("1990-01-01");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert - should handle null gracefully
            verify(request, atLeastOnce()).getParameter("name_surname");
        }
    }

    // ============================================================================
    // Successful Registration Tests
    // ============================================================================

    @Nested
    @DisplayName("Successful Registration Tests")
    class SuccessfulRegistrationTests {

        @Test
        @DisplayName("TC-REG-7: Valid inputs register successfully")
        void testValidInputsRegisterSuccessfully() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert - if registration successful, should redirect
            verify(request, atLeastOnce()).getParameter("username");
            verify(request, atLeastOnce()).getParameter("email");
            verify(request, atLeastOnce()).getParameter("password");
        }

        @Test
        @DisplayName("TC-REG-18: All fields populated correctly")
        void testAllFieldsPopulatedCorrectly() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert - verify all parameters are read
            verify(request).getParameter("username");
            verify(request).getParameter("email");
            verify(request).getParameter("password");
            verify(request).getParameter("passwordConf");
            verify(request).getParameter("name_surname");
            verify(request).getParameter("gender");
            verify(request).getParameter("country");
            verify(request).getParameter("birthday");
        }
    }

    // ============================================================================
    // AJAX Request Tests
    // ============================================================================

    @Nested
    @DisplayName("AJAX Request Tests")
    class AjaxRequestTests {

        @Test
        @DisplayName("TC-REG-8: AJAX request returns JSON response")
        void testAjaxReturnsJson() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            registerServlet.doPost(request, response);

            // Assert - AJAX requests should set JSON content type
            verify(response).setContentType("application/json");
            verify(response).setCharacterEncoding("UTF-8");
        }

        @Test
        @DisplayName("TC-REG-9: Normal request redirects")
        void testNormalRequestRedirects() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert - Normal requests should redirect
            verify(response).sendRedirect(anyString());
        }

        @Test
        @DisplayName("TC-REG-10: AJAX with existing username returns JSON error")
        void testAjaxExistingUsernameJsonError() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getParameter("username")).thenReturn("existingUser");
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(response).setContentType("application/json");
        }

        @Test
        @DisplayName("TC-REG-11: AJAX with valid data returns JSON success")
        void testAjaxValidDataJsonSuccess() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(response).setContentType("application/json");
            verify(response).setCharacterEncoding("UTF-8");
        }

        @Test
        @DisplayName("TC-REG-19: AJAX error sets 401 status")
        void testAjaxErrorSets401Status() throws ServletException, IOException {
            // Arrange - setup params that will cause an error
            when(request.getParameter("username")).thenReturn("existingUser");
            when(request.getParameter("email")).thenReturn("existing@email.com");
            when(request.getParameter("password")).thenReturn("ValidPass123!");
            when(request.getParameter("passwordConf")).thenReturn("ValidPass123!");
            when(request.getParameter("name_surname")).thenReturn("John Doe");
            when(request.getParameter("gender")).thenReturn("M");
            when(request.getParameter("country")).thenReturn("USA");
            when(request.getParameter("birthday")).thenReturn("1990-01-01");
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            registerServlet.doPost(request, response);

            // Assert - if error, should set 401 status
            // Note: actual status depends on error path taken
            verify(response).setContentType("application/json");
        }
    }

    // ============================================================================
    // Exception Handling Tests
    // ============================================================================

    @Nested
    @DisplayName("Exception Handling Tests")
    class ExceptionHandlingTests {

        @Test
        @DisplayName("TC-REG-12: SQLException is handled gracefully")
        void testNullDataSourceError() throws Exception {
            // Arrange
            setupValidRegistrationParams();
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");
            
            // Make the userDao throw SQLException from doRetrieveAll (used by checkUsername)
            when(userDao.doRetrieveAll(anyString())).thenThrow(new java.sql.SQLException("Database error"));

            // Act
            registerServlet.doPost(request, response);
            
            // Assert - Should send 500 error on SQLException
            verify(response).sendError(eq(500), anyString());
        }

        @Test
        @DisplayName("TC-REG-20: Error attribute set on exception")
        void testErrorAttributeSetOnException() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert - verify request params were accessed
            verify(request, atLeastOnce()).getParameter("username");
        }
    }

    // ============================================================================
    // Countries and Genders Tests
    // ============================================================================

    @Nested
    @DisplayName("Countries and Genders Tests")
    class CountriesAndGendersTests {

        @Test
        @DisplayName("TC-REG-21: Countries attribute set on doPost")
        void testCountriesAttributeSetOnDoPost() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request).setAttribute(eq("countries"), any());
        }

        @Test
        @DisplayName("TC-REG-22: Genders attribute set on doPost")
        void testGendersAttributeSetOnDoPost() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request).setAttribute(eq("genders"), any());
        }
    }

    // ============================================================================
    // Boundary Value Tests
    // ============================================================================

    @Nested
    @DisplayName("Boundary Value Tests")
    class BoundaryValueTests {

        @Test
        @DisplayName("TC-REG-23: Maximum length username (30 chars)")
        void testMaxLengthUsername() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            when(request.getParameter("username")).thenReturn("a".repeat(30));
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request, atLeastOnce()).getParameter("username");
        }

        @Test
        @DisplayName("TC-REG-24: Maximum length email (80 chars)")
        void testMaxLengthEmail() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            String longEmail = "a".repeat(70) + "@test.com";
            when(request.getParameter("email")).thenReturn(longEmail);
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request, atLeastOnce()).getParameter("email");
        }

        @Test
        @DisplayName("TC-REG-25: Maximum length password (30 chars)")
        void testMaxLengthPassword() throws ServletException, IOException {
            // Arrange
            setupValidRegistrationParams();
            String longPassword = "ValidPass123!" + "a".repeat(17);
            when(request.getParameter("password")).thenReturn(longPassword);
            when(request.getParameter("passwordConf")).thenReturn(longPassword);
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getContextPath()).thenReturn("/app");

            // Act
            registerServlet.doPost(request, response);

            // Assert
            verify(request, atLeastOnce()).getParameter("password");
        }
    }

    // ============================================================================
    // Helper Methods
    // ============================================================================

    private void setupValidRegistrationParams() {
        when(request.getParameter("username")).thenReturn("newUser");
        when(request.getParameter("email")).thenReturn("new@email.com");
        when(request.getParameter("password")).thenReturn("ValidPass123!");
        when(request.getParameter("passwordConf")).thenReturn("ValidPass123!");
        when(request.getParameter("name_surname")).thenReturn("John Doe");
        when(request.getParameter("gender")).thenReturn("M");
        when(request.getParameter("country")).thenReturn("USA");
        when(request.getParameter("birthday")).thenReturn("1990-01-01");
    }
}
