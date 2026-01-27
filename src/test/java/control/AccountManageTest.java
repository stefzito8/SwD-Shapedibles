package control;

import categories.UnitTest;
import model.bean.UserBean;
import model.dao.IUserDao;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.mockito.junit.jupiter.MockitoSettings;
import org.mockito.quality.Strictness;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletContext;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import javax.sql.DataSource;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Unit tests for AccountManage controller.
 * 
 * Testing Level: Unit
 * Technique: White-Box (Statement Testing, Branch Testing) with Mocking
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@MockitoSettings(strictness = Strictness.LENIENT)
@DisplayName("AccountManage Controller Unit Tests")
public class AccountManageTest {

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

    private AccountManage accountManageServlet;

    @BeforeEach
    void setUp() throws Exception {
        accountManageServlet = new AccountManage() {
            @Override
            public ServletContext getServletContext() {
                return servletContext;
            }
            
            @Override
            protected IUserDao createUserDao(DataSource ds) {
                return userDao;
            }
        };
        
        when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
        when(servletContext.getRequestDispatcher(anyString())).thenReturn(requestDispatcher);
    }

    // ============================================================================
    // doGet Tests
    // ============================================================================

    @Nested
    @DisplayName("doGet Tests")
    class DoGetTests {

        @Test
        @DisplayName("doGet delegates to doPost")
        void testDoGetDelegatesToDoPost() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(userDao.doRetrieveAll(anyString())).thenReturn(new ArrayList<>());

            accountManageServlet.doGet(request, response);

            verify(servletContext).getRequestDispatcher("/WEB-INF/jsp/admin/accountManagement.jsp");
        }
    }

    // ============================================================================
    // doPost Tests - Action null
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - No Action")
    class DoPostNoActionTests {

        @Test
        @DisplayName("No action - retrieve all users and forward")
        void testNoAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            Collection<UserBean> users = new ArrayList<>();
            users.add(createTestUser("user1"));
            when(userDao.doRetrieveAll(anyString())).thenReturn(users);

            accountManageServlet.doPost(request, response);

            // Verify removeAttribute is called before setAttribute (kills VoidMethodCallMutator mutation line 71)
            verify(request).removeAttribute("users");
            verify(request).setAttribute(eq("users"), any());
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // doPost Tests - Admin Action
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - Admin Action")
    class DoPostAdminActionTests {

        @Test
        @DisplayName("Admin action - promote user to admin")
        void testAdminAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("admin");
            when(request.getParameter("username")).thenReturn("testuser");
            
            UserBean user = createTestUser("testuser");
            when(userDao.doRetrieveByKey("testuser")).thenReturn(user);
            when(userDao.doRetrieveAll(anyString())).thenReturn(new ArrayList<>());

            accountManageServlet.doPost(request, response);

            verify(userDao).doRetrieveByKey("testuser");
            verify(userDao).doDelete("testuser");
            verify(userDao).doSave(argThat(u -> u.getUserAdmin() == 1));
        }

        @Test
        @DisplayName("Admin action - case insensitive")
        void testAdminActionCaseInsensitive() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("ADMIN");
            when(request.getParameter("username")).thenReturn("testuser");
            
            UserBean user = createTestUser("testuser");
            when(userDao.doRetrieveByKey("testuser")).thenReturn(user);
            when(userDao.doRetrieveAll(anyString())).thenReturn(new ArrayList<>());

            accountManageServlet.doPost(request, response);

            verify(userDao).doSave(any(UserBean.class));
        }
    }

    // ============================================================================
    // doPost Tests - Delete Action
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - Delete Action")
    class DoPostDeleteActionTests {

        @Test
        @DisplayName("Delete action - delete user")
        void testDeleteAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("delete");
            when(request.getParameter("username")).thenReturn("userToDelete");
            when(userDao.doRetrieveAll(anyString())).thenReturn(new ArrayList<>());

            accountManageServlet.doPost(request, response);

            verify(userDao).doDelete("userToDelete");
        }

        @Test
        @DisplayName("Delete action - case insensitive")
        void testDeleteActionCaseInsensitive() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DELETE");
            when(request.getParameter("username")).thenReturn("userToDelete");
            when(userDao.doRetrieveAll(anyString())).thenReturn(new ArrayList<>());

            accountManageServlet.doPost(request, response);

            verify(userDao).doDelete("userToDelete");
        }
    }

    // ============================================================================
    // doPost Tests - SQLException Handling
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - SQLException Handling")
    class DoPostSQLExceptionTests {

        @Test
        @DisplayName("SQLException during action - sends error")
        void testSQLExceptionDuringAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("admin");
            when(request.getParameter("username")).thenReturn("testuser");
            when(userDao.doRetrieveByKey(anyString())).thenThrow(new SQLException("DB Error"));
            when(userDao.doRetrieveAll(anyString())).thenReturn(new ArrayList<>());

            accountManageServlet.doPost(request, response);

            verify(response).sendError(eq(500), contains("Error"));
        }

        @Test
        @DisplayName("SQLException during retrieve all - sends error")
        void testSQLExceptionDuringRetrieveAll() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(userDao.doRetrieveAll(anyString())).thenThrow(new SQLException("DB Error"));

            accountManageServlet.doPost(request, response);

            verify(response).sendError(eq(500), contains("Error"));
        }
    }

    // ============================================================================
    // Helper Methods
    // ============================================================================

    private UserBean createTestUser(String username) {
        UserBean user = new UserBean();
        user.setUsername(username);
        user.setEmail(username + "@test.com");
        user.setPass("password");
        user.setNomeCognome("Test User");
        user.setSesso("M");
        user.setPaese("Italy");
        user.setDataNascita("1990-01-01");
        user.setUserAdmin(0);
        return user;
    }
}
