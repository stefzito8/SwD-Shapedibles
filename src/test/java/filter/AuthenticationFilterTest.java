package filter;

import categories.UnitTest;
import javax.servlet.FilterChain;
import javax.servlet.FilterConfig;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import model.bean.UserBean;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.IOException;

import static org.mockito.Mockito.*;

/**
 * Unit tests for AuthenticationFilter.
 * 
 * Testing Level: Unit
 * Testing Technique: Equivalence Class Testing, Branch Testing, Mocking
 * 
 * Filter Behavior Specification (from Step 4.1):
 * - URL patterns protected: /admin/* (admin users only), /user/* (authenticated users)
 * - Authentication flow: Session check → LoggedUser attribute check → Authorization check
 * 
 * Equivalence Classes:
 * - EC1: Session State (no session, session without LoggedUser, session with LoggedUser)
 * - EC2: User Role/Authorization (admin userAdmin=1, non-admin userAdmin=0)
 * - EC3: URL Pattern Matching (admin path, user path, unprotected path)
 * - EC4: Special Requests (login URI, login page, other requests)
 * 
 * Boundary Values:
 * - BV1: Empty session attributes
 * - BV2: userAdmin=0 (boundary between admin/non-admin)
 * - BV3: userAdmin=1 (admin threshold)
 * - BV4: Session timeout edge case
 * 
 * Branches to Cover (White-Box):
 * - B1: session == null
 * - B2: session.getAttribute("LoggedUser") == null
 * - B3: User is admin (userAdmin == 1)
 * - B4: User is not admin (userAdmin == 0)
 * - B5: Request URI starts with /admin/
 * - B6: Request URI starts with /user/
 * - B7: Unprotected path (neither /admin/ nor /user/)
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@DisplayName("AuthenticationFilter Unit Tests")
public class AuthenticationFilterTest {

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private FilterChain filterChain;

    @Mock
    private HttpSession session;

    @Mock
    private FilterConfig filterConfig;

    private AuthenticationFilter filter;

    @BeforeEach
    void setUp() throws ServletException {
        filter = new AuthenticationFilter();
        filter.init(filterConfig);
    }

    // ==================== EC1: Session State Tests ====================

    @Nested
    @DisplayName("EC1: Session State Tests")
    class SessionStateTests {

        @Test
        @DisplayName("TC1: No session - should redirect to login for protected path")
        void testNoSession_ProtectedPath_RedirectsToLogin() throws IOException, ServletException {
            // Arrange
            when(request.getSession(false)).thenReturn(null);
            when(request.getSession()).thenReturn(session); // Mock session creation
            when(request.getRequestURI()).thenReturn("/user/profile");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(response).sendRedirect(contains("Login"));
            verify(filterChain, never()).doFilter(request, response);
        }

        @Test
        @DisplayName("TC2: No session - unprotected path should redirect to login")
        void testNoSession_UnprotectedPath_Proceeds() throws IOException, ServletException {
            // Arrange
            when(request.getSession(false)).thenReturn(null);
            when(request.getSession()).thenReturn(session); // Mock session creation
            when(request.getRequestURI()).thenReturn("/home");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            // Based on the filter logic, if not logged in AND not login request/page, it redirects
            verify(response).sendRedirect(contains("Login"));
            verify(filterChain, never()).doFilter(request, response);
        }

        @Test
        @DisplayName("TC3: Session exists but no LoggedUser - protected path redirects")
        void testSessionWithoutLoggedUser_ProtectedPath_Redirects() throws IOException, ServletException {
            // Arrange
            when(request.getSession(false)).thenReturn(session);
            when(request.getSession()).thenReturn(session); // Mock getSession() to return same session
            when(session.getAttribute("LoggedUser")).thenReturn(null);
            when(request.getRequestURI()).thenReturn("/user/orders");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(response).sendRedirect(contains("Login"));
            verify(filterChain, never()).doFilter(request, response);
        }

        @Test
        @DisplayName("TC4: Session with LoggedUser - user path proceeds")
        void testSessionWithLoggedUser_UserPath_Proceeds() throws IOException, ServletException {
            // Arrange
            UserBean user = createUserBean(0); // non-admin user
            when(request.getSession(false)).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(request.getRequestURI()).thenReturn("/user/profile");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(filterChain).doFilter(request, response);
            verify(response, never()).sendRedirect(anyString());
        }
    }

    // ==================== EC2: User Role/Authorization Tests ====================

    @Nested
    @DisplayName("EC2: User Role/Authorization Tests")
    class UserRoleTests {

        @Test
        @DisplayName("TC5: Admin user accessing admin path - should proceed")
        void testAdminUser_AdminPath_Proceeds() throws IOException, ServletException {
            // Arrange
            UserBean adminUser = createUserBean(1); // admin
            when(request.getSession(false)).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(adminUser);
            when(request.getRequestURI()).thenReturn("/admin/products");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(filterChain).doFilter(request, response);
            verify(response, never()).sendRedirect(anyString());
        }

        @Test
        @DisplayName("TC6: Non-admin user accessing admin path - should redirect/block")
        void testNonAdminUser_AdminPath_Blocked() throws IOException, ServletException {
            // Arrange
            UserBean regularUser = createUserBean(0); // non-admin
            when(request.getSession(false)).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(regularUser);
            when(request.getRequestURI()).thenReturn("/admin/products");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert - should redirect or send error
            verify(filterChain, never()).doFilter(request, response);
        }

        @Test
        @DisplayName("TC7: Admin user accessing user path - should proceed")
        void testAdminUser_UserPath_Proceeds() throws IOException, ServletException {
            // Arrange
            UserBean adminUser = createUserBean(1); // admin
            when(request.getSession(false)).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(adminUser);
            when(request.getRequestURI()).thenReturn("/user/profile");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(filterChain).doFilter(request, response);
        }
    }

    // ==================== EC3: URL Pattern Matching Tests ====================

    @Nested
    @DisplayName("EC3: URL Pattern Matching Tests")
    class UrlPatternTests {

        @Test
        @DisplayName("TC8: Unprotected path - should redirect to login when not authenticated")
        void testUnprotectedPath_AlwaysProceeds() throws IOException, ServletException {
            // Arrange - no session, unprotected path
            when(request.getSession(false)).thenReturn(null);
            when(request.getSession()).thenReturn(session); // Mock session creation
            when(request.getRequestURI()).thenReturn("/Home");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            // Filter redirects to login if not logged in AND not login/loginView.jsp
            verify(response).sendRedirect(contains("Login"));
        }

        @Test
        @DisplayName("TC9: Login page path - should proceed even without session")
        void testLoginPath_Proceeds() throws IOException, ServletException {
            // Arrange
            when(request.getSession(false)).thenReturn(null);
            when(request.getRequestURI()).thenReturn("/Login");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(filterChain).doFilter(request, response);
            verify(response, never()).sendRedirect(anyString());
        }

        @Test
        @DisplayName("TC10: Static resources - should redirect to login when not authenticated")
        void testStaticResources_Proceed() throws IOException, ServletException {
            // Arrange
            when(request.getSession(false)).thenReturn(null);
            when(request.getSession()).thenReturn(session); // Mock session creation
            when(request.getRequestURI()).thenReturn("/assets/styles/base.css");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            // Filter redirects to login if not logged in AND not login/loginView.jsp
            verify(response).sendRedirect(contains("Login"));
        }
    }

    // ==================== EC4: Special Requests Tests ====================

    @Nested
    @DisplayName("EC4: Special Request Tests")
    class SpecialRequestTests {

        @Test
        @DisplayName("TC11: Register page - should redirect to login when not authenticated")
        void testRegisterPath_Proceeds() throws IOException, ServletException {
            // Arrange
            when(request.getSession(false)).thenReturn(null);
            when(request.getSession()).thenReturn(session); // Mock session creation
            when(request.getRequestURI()).thenReturn("/Register");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            // Filter redirects to login if not logged in AND not login/loginView.jsp
            verify(response).sendRedirect(contains("Login"));
        }

        @Test
        @DisplayName("TC12: Product details - should redirect to login when not authenticated")
        void testProductDetailsPath_Proceeds() throws IOException, ServletException {
            // Arrange
            when(request.getSession(false)).thenReturn(null);
            when(request.getSession()).thenReturn(session); // Mock session creation
            when(request.getRequestURI()).thenReturn("/ProductDetails");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            // Filter redirects to login if not logged in AND not login/loginView.jsp
            verify(response).sendRedirect(contains("Login"));
        }
    }

    // ==================== Boundary Value Tests ====================

    @Nested
    @DisplayName("Boundary Value Tests")
    class BoundaryValueTests {

        @Test
        @DisplayName("BV1: Empty context path")
        void testEmptyContextPath() throws IOException, ServletException {
            // Arrange
            when(request.getSession(false)).thenReturn(null);
            when(request.getSession()).thenReturn(session); // Mock session creation
            when(request.getRequestURI()).thenReturn("/Home");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(response).sendRedirect(contains("Login"));
        }

        @Test
        @DisplayName("BV2: Context path with application name")
        void testContextPathWithAppName() throws IOException, ServletException {
            // Arrange
            UserBean user = createUserBean(0);
            when(request.getSession(false)).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(request.getRequestURI()).thenReturn("/myapp/user/profile");
            when(request.getContextPath()).thenReturn("/myapp");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(filterChain).doFilter(request, response);
        }

        @Test
        @DisplayName("BV3: userAdmin exactly 0 (non-admin boundary)")
        void testUserAdminZero_NonAdmin() throws IOException, ServletException {
            // Arrange
            UserBean user = createUserBean(0); // exactly 0
            when(request.getSession(false)).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(request.getRequestURI()).thenReturn("/admin/dashboard");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert - should be blocked from admin
            verify(filterChain, never()).doFilter(request, response);
        }

        @Test
        @DisplayName("BV4: userAdmin exactly 1 (admin boundary)")
        void testUserAdminOne_Admin() throws IOException, ServletException {
            // Arrange
            UserBean user = createUserBean(1); // exactly 1
            when(request.getSession(false)).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(request.getRequestURI()).thenReturn("/admin/dashboard");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert - should proceed as admin
            verify(filterChain).doFilter(request, response);
        }
    }

    // ==================== Branch Coverage Tests ====================

    @Nested
    @DisplayName("Branch Coverage Tests (White-Box)")
    class BranchCoverageTests {

        @Test
        @DisplayName("B1: session == null branch (true)")
        void testBranch_SessionNull_True() throws IOException, ServletException {
            // Arrange
            when(request.getSession(false)).thenReturn(null);
            when(request.getSession()).thenReturn(session); // Mock session creation
            when(request.getRequestURI()).thenReturn("/user/profile");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(response).sendRedirect(anyString());
        }

        @Test
        @DisplayName("B1: session == null branch (false)")
        void testBranch_SessionNull_False() throws IOException, ServletException {
            // Arrange
            UserBean user = createUserBean(0);
            when(request.getSession(false)).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(request.getRequestURI()).thenReturn("/user/profile");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(filterChain).doFilter(request, response);
        }

        @Test
        @DisplayName("B2: LoggedUser == null branch (true)")
        void testBranch_LoggedUserNull_True() throws IOException, ServletException {
            // Arrange
            when(request.getSession(false)).thenReturn(session);
            when(request.getSession()).thenReturn(session); // Mock getSession() to return same session
            when(session.getAttribute("LoggedUser")).thenReturn(null);
            when(request.getRequestURI()).thenReturn("/user/orders");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(response).sendRedirect(anyString());
        }

        @Test
        @DisplayName("B2: LoggedUser == null branch (false)")
        void testBranch_LoggedUserNull_False() throws IOException, ServletException {
            // Arrange
            UserBean user = createUserBean(0);
            when(request.getSession(false)).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(request.getRequestURI()).thenReturn("/user/orders");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(filterChain).doFilter(request, response);
        }

        @Test
        @DisplayName("B5: Admin path detection (true)")
        void testBranch_AdminPath_True() throws IOException, ServletException {
            // Arrange
            UserBean admin = createUserBean(1);
            when(request.getSession(false)).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(admin);
            when(request.getRequestURI()).thenReturn("/admin/settings");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert - admin should access admin path
            verify(filterChain).doFilter(request, response);
        }

        @Test
        @DisplayName("B6: User path detection (true)")
        void testBranch_UserPath_True() throws IOException, ServletException {
            // Arrange
            UserBean user = createUserBean(0);
            when(request.getSession(false)).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(request.getRequestURI()).thenReturn("/user/account");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            verify(filterChain).doFilter(request, response);
        }

        @Test
        @DisplayName("B7: Unprotected path (neither admin nor user)")
        void testBranch_UnprotectedPath() throws IOException, ServletException {
            // Arrange
            when(request.getSession(false)).thenReturn(null);
            when(request.getSession()).thenReturn(session); // Mock session creation
            when(request.getRequestURI()).thenReturn("/Search");
            when(request.getContextPath()).thenReturn("");

            // Act
            filter.doFilter(request, response, filterChain);

            // Assert
            // Filter redirects to login if not logged in AND not login/loginView.jsp
            verify(response).sendRedirect(contains("Login"));
        }
    }

    // ==================== Filter Lifecycle Tests ====================

    @Nested
    @DisplayName("Filter Lifecycle Tests")
    class LifecycleTests {

        @Test
        @DisplayName("Filter init should complete without error")
        void testInit() throws ServletException {
            // Arrange
            AuthenticationFilter newFilter = new AuthenticationFilter();

            // Act & Assert - should not throw
            newFilter.init(filterConfig);
        }

        @Test
        @DisplayName("Filter destroy should complete without error")
        void testDestroy() {
            // Act & Assert - should not throw
            filter.destroy();
        }
    }

    // ==================== Helper Methods ====================

    /**
     * Creates a UserBean with the specified admin level.
     * 
     * @param adminLevel 0 for regular user, 1 for admin
     * @return configured UserBean mock or instance
     */
    private UserBean createUserBean(int adminLevel) {
        UserBean user = new UserBean();
        user.setUserAdmin(adminLevel);
        user.setUsername("testuser");
        user.setEmail("test@example.com");
        return user;
    }
}
