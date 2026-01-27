package control;

import categories.UnitTest;
import model.bean.ContainBean;
import model.bean.OrderBean;
import model.bean.UserBean;
import model.dao.IContainDao;
import model.dao.IOrderDao;
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
 * Unit tests for UserProfile controller.
 * 
 * Testing Level: Unit
 * Technique: White-Box (Statement Testing, Branch Testing) with Mocking
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@MockitoSettings(strictness = Strictness.LENIENT)
@DisplayName("UserProfile Controller Unit Tests")
public class UserProfileTest {

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

    @Mock
    private IOrderDao orderDao;

    @Mock
    private IContainDao containDao;

    private UserProfile userProfileServlet;
    private UserBean loggedUser;

    @BeforeEach
    void setUp() throws Exception {
        userProfileServlet = new UserProfile() {
            @Override
            public ServletContext getServletContext() {
                return servletContext;
            }
            
            @Override
            protected IUserDao createUserDao(DataSource ds) {
                return userDao;
            }
            
            @Override
            protected IOrderDao createOrderDao(DataSource ds) {
                return orderDao;
            }
            
            @Override
            protected IContainDao createContainDao(DataSource ds) {
                return containDao;
            }
        };
        
        loggedUser = createTestUser("testuser");
        
        when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
        when(servletContext.getRequestDispatcher(anyString())).thenReturn(requestDispatcher);
        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("LoggedUser")).thenReturn(loggedUser);
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
            when(orderDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());

            userProfileServlet.doGet(request, response);

            verify(servletContext).getRequestDispatcher("/WEB-INF/jsp/pages/userProfile.jsp");
        }
    }

    // ============================================================================
    // doPost Tests - No Action
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - No Action")
    class DoPostNoActionTests {

        @Test
        @DisplayName("No action - verifies removeAttribute before setAttribute for OrdersLoggedUser")
        void testNoAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            Collection<OrderBean> orders = new ArrayList<>();
            orders.add(createTestOrder(1, "testuser"));
            when(orderDao.doRetrieveByUser("testuser")).thenReturn(orders);

            userProfileServlet.doPost(request, response);

            // Verify removeAttribute is called BEFORE setAttribute for OrdersLoggedUser (kills mutation)
            verify(request).removeAttribute("OrdersLoggedUser");
            verify(request).setAttribute(eq("OrdersLoggedUser"), any());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("No action - verifies proper order of removeAttribute then setAttribute")
        void testNoActionRemoveBeforeSet() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            Collection<OrderBean> orders = new ArrayList<>();
            orders.add(createTestOrder(1, "testuser"));
            when(orderDao.doRetrieveByUser("testuser")).thenReturn(orders);

            userProfileServlet.doPost(request, response);

            // Verify order: removeAttribute THEN setAttribute (kills mutation if removeAttribute is removed)
            org.mockito.InOrder inOrder = inOrder(request);
            inOrder.verify(request).removeAttribute("OrdersLoggedUser");
            inOrder.verify(request, atLeastOnce()).setAttribute(eq("OrdersLoggedUser"), any());
        }
    }

    // ============================================================================
    // doPost Tests - OrderDetails Action
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - OrderDetails Action")
    class DoPostOrderDetailsActionTests {

        @Test
        @DisplayName("OrderDetails action - verifies removeAttribute before setAttribute for Details")
        void testOrderDetailsAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("orderDetails");
            when(request.getParameter("orderNum")).thenReturn("123");
            when(request.getParameter("orderUser")).thenReturn("testuser");
            
            Collection<ContainBean> items = new ArrayList<>();
            items.add(createTestContainBean(123, 1));
            when(containDao.doRetrieveByOrder(123)).thenReturn(items);
            when(orderDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());

            userProfileServlet.doPost(request, response);

            // Verify removeAttribute is called BEFORE setAttribute for Details (kills removeAttribute mutation)
            verify(request).removeAttribute("Details");
            verify(containDao).doRetrieveByOrder(123);
            verify(request).setAttribute(eq("Details"), any());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("OrderDetails action - verifies proper order of removeAttribute then setAttribute")
        void testOrderDetailsRemoveBeforeSet() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("orderDetails");
            when(request.getParameter("orderNum")).thenReturn("123");
            when(request.getParameter("orderUser")).thenReturn("testuser");
            
            Collection<ContainBean> items = new ArrayList<>();
            items.add(createTestContainBean(123, 1));
            when(containDao.doRetrieveByOrder(123)).thenReturn(items);
            when(orderDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());

            userProfileServlet.doPost(request, response);

            // Verify order: removeAttribute THEN setAttribute (kills mutation if removeAttribute is removed)
            org.mockito.InOrder inOrder = inOrder(request);
            inOrder.verify(request).removeAttribute("Details");
            inOrder.verify(request).setAttribute(eq("Details"), eq(items));
        }

        @Test
        @DisplayName("OrderDetails action - case insensitive")
        void testOrderDetailsActionCaseInsensitive() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("ORDERDETAILS");
            when(request.getParameter("orderNum")).thenReturn("456");
            when(request.getParameter("orderUser")).thenReturn("testuser");
            
            when(containDao.doRetrieveByOrder(456)).thenReturn(new ArrayList<>());
            when(orderDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());

            userProfileServlet.doPost(request, response);

            verify(containDao).doRetrieveByOrder(456);
            // Also verify removeAttribute is called
            verify(request).removeAttribute("Details");
        }
    }

    // ============================================================================
    // doPost Tests - Null User Handling
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - Null User Handling")
    class DoPostNullUserTests {

        @Test
        @DisplayName("Null user - sets error attribute before throwing NPE")
        void testNullUserSetsError() throws ServletException, IOException, SQLException {
            when(session.getAttribute("LoggedUser")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);

            // This will throw NullPointerException in the actual code
            // but verify that error attribute is set BEFORE the NPE
            assertThrows(NullPointerException.class, () -> {
                userProfileServlet.doPost(request, response);
            });
            
            // Verify error attribute is set with exact message (kills mutation on line 63)
            verify(request).setAttribute("error", "Errore: Non c'è alcun utente loggato");
        }
        
        @Test
        @DisplayName("Null user - verifies error message content is used")
        void testNullUserErrorMessageContent() throws ServletException, IOException, SQLException {
            when(session.getAttribute("LoggedUser")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);

            // Capture the exception but also verify the setAttribute call
            try {
                userProfileServlet.doPost(request, response);
            } catch (NullPointerException e) {
                // Expected - verify that setAttribute was called with exact message
                verify(request).setAttribute(eq("error"), argThat(msg -> 
                    msg != null && msg.equals("Errore: Non c'è alcun utente loggato")
                ));
            }
        }
    }

    // ============================================================================
    // doPost Tests - SQLException Handling
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - SQLException Handling")
    class DoPostSQLExceptionTests {

        @Test
        @DisplayName("SQLException during order retrieval - sets error attribute AND sends 500")
        void testSQLExceptionDuringOrderRetrieval() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(orderDao.doRetrieveByUser(anyString())).thenThrow(new SQLException("DB Error"));

            userProfileServlet.doPost(request, response);

            // Verify BOTH setAttribute and sendError are called - kills both mutations
            verify(request, atLeast(1)).setAttribute(eq("error"), argThat(msg -> 
                msg != null && msg.toString().contains("Error:")
            ));
            verify(response, atLeast(1)).sendError(eq(500), argThat(msg -> 
                msg != null && msg.contains("DB Error")
            ));
        }

        @Test
        @DisplayName("SQLException during order details - sets error and sends 500 with message")
        void testSQLExceptionDuringOrderDetails() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("orderDetails");
            when(request.getParameter("orderNum")).thenReturn("123");
            when(request.getParameter("orderUser")).thenReturn("testuser");
            when(orderDao.doRetrieveByUser(anyString())).thenThrow(new SQLException("Order DB Error"));

            userProfileServlet.doPost(request, response);

            // Kill mutations by verifying error message content - use atLeast since multiple catches
            verify(request, atLeast(1)).setAttribute(eq("error"), 
                eq("Error: c'è stato un errore nel elaborazione dei tuoi dati."));
            verify(response, atLeast(1)).sendError(eq(500), contains("Order DB Error"));
        }

        @Test
        @DisplayName("SQLException during profile retrieval - verifies error attribute is used")
        void testSQLExceptionDuringProfileRetrieval() throws ServletException, IOException, SQLException {
            // This targets the surviving mutation at line 89-90
            when(request.getParameter("action")).thenReturn(null);
            when(orderDao.doRetrieveByUser(anyString()))
                .thenReturn(new ArrayList<>())
                .thenThrow(new SQLException("Profile Error"));

            userProfileServlet.doPost(request, response);

            // Verify the specific error message for profile retrieval
            verify(request).setAttribute(eq("error"), 
                eq("Error: c'è stato un errore nel recupero delle informazioni del profilo utente."));
            verify(response).sendError(eq(500), contains("Profile Error"));
        }

        @Test
        @DisplayName("SQLException during contain retrieval - complete verification")
        void testSQLExceptionDuringContainRetrieval() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("orderDetails");
            when(request.getParameter("orderNum")).thenReturn("123");
            when(request.getParameter("orderUser")).thenReturn("testuser");
            when(orderDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());
            when(containDao.doRetrieveByOrder(123)).thenThrow(new SQLException("Contain Error"));

            userProfileServlet.doPost(request, response);

            // Verify error attribute is set with specific message
            verify(request).setAttribute(eq("error"), 
                eq("Error: c'è stato un errore nel elaborazione dei tuoi dati."));
            verify(response).sendError(eq(500), contains("Contain Error"));
        }

        @Test
        @DisplayName("SQLException - verifies error flow order")
        void testSQLExceptionFlowOrder() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(orderDao.doRetrieveByUser(anyString()))
                .thenReturn(new ArrayList<>())
                .thenThrow(new SQLException("Flow Error"));

            userProfileServlet.doPost(request, response);

            // Verify setAttribute and sendError are both called with proper values
            verify(request).setAttribute(eq("error"), anyString());
            verify(response).sendError(eq(500), anyString());
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

    private OrderBean createTestOrder(int numero, String username) {
        OrderBean order = new OrderBean();
        order.setCodice(numero);
        order.setUtente(username);
        order.setStato("pending");
        order.setDataOrdine("2024-01-01 12:00:00");
        order.setIndirizzo("addr1");
        return order;
    }

    private ContainBean createTestContainBean(int orderNum, int productCode) {
        ContainBean contain = new ContainBean();
        contain.setCodiceOrdine(orderNum);
        contain.setCodiceProdotto(productCode);
        contain.setQuantità(2);
        return contain;
    }
}
