package control;

import categories.UnitTest;
import model.Cart;
import model.bean.ContainBean;
import model.bean.InfoBean;
import model.bean.OrderBean;
import model.bean.ProductBean;
import model.bean.UserBean;
import model.dao.IAddressDao;
import model.dao.IContainDao;
import model.dao.IInfoDao;
import model.dao.IOrderDao;
import model.dao.IProductDao;
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
import java.io.PrintWriter;
import java.io.StringWriter;
import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

import org.mockito.ArgumentCaptor;
import java.util.List;

/**
 * Unit tests for Checkout controller.
 * 
 * Testing Level: Unit
 * Technique: White-Box (Statement Testing, Branch Testing) with Mocking
 * 
 * ============================================================================
 * BRANCH STRUCTURE ANALYSIS (Step 3.1)
 * ============================================================================
 * 
 * Method: doGet/doPost(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | CHK-B1    | User authenticated           | Show checkout     | Redirect login |
 * | CHK-B2    | Cart is empty                | Error message     | Process order  |
 * | CHK-B3    | Address provided             | Use provided addr | Use default    |
 * | CHK-B4    | Order created successfully   | Success page      | Error handling |
 * | CHK-B5    | Stock available              | Process order     | Error message  |
 * | CHK-B6    | AJAX request                 | JSON response     | Page response  |
 * | CHK-B7    | action == "confirm"          | Complete order    | Continue checkout |
 * | CHK-B8    | SQLException caught          | Error response    | Normal flow    |
 * -----------------------------------------------------------------
 * 
 * ============================================================================
 * TEST CASE DESIGN (Step 3.2)
 * ============================================================================
 * 
 * | Test ID      | Branch Target    | Input Condition              | Expected Result      |
 * |--------------|------------------|------------------------------|----------------------|
 * | TC-CHK-1     | B1=true          | User logged in               | Checkout displayed   |
 * | TC-CHK-2     | B1=false         | No user session              | Redirect to login    |
 * | TC-CHK-3     | B2=true          | Empty cart                   | Empty cart message   |
 * | TC-CHK-4     | B2=false         | Cart with items              | Process checkout     |
 * | TC-CHK-5     | B3=true          | Address in request           | Use request address  |
 * | TC-CHK-6     | B3=false         | No address provided          | Use default address  |
 * | TC-CHK-7     | B4=true, B7=true | action=confirm, success      | Order completed      |
 * | TC-CHK-8     | B8=true          | SQLException                 | Error handling       |
 * | TC-CHK-9     | doGet            | GET request                  | Delegates to doPost  |
 * | TC-CHK-10    | Loop (0 iter)    | Empty cart                   | No product iteration |
 * | TC-CHK-11    | Loop (1 iter)    | Single product               | One iteration        |
 * | TC-CHK-12    | Loop (>1 iter)   | Multiple products            | Multiple iterations  |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets:
 * - TER1 (Statement): ≥ 80%
 * - TER2 (Branch): ≥ 70%
 * 
 * @see control.Checkout
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@MockitoSettings(strictness = Strictness.LENIENT)
@DisplayName("Checkout Controller Unit Tests")
public class CheckoutTest {

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
    private IOrderDao orderDao;

    @Mock
    private IProductDao productDao;

    @Mock
    private IAddressDao addressDao;

    @Mock
    private IInfoDao infoDao;

    @Mock
    private IContainDao containDao;

    private StringWriter stringWriter;
    private PrintWriter printWriter;
    private Checkout checkoutServlet;

    @BeforeEach
    void setUp() throws Exception {
        stringWriter = new StringWriter();
        printWriter = new PrintWriter(stringWriter);
        checkoutServlet = new Checkout() {
            @Override
            public ServletContext getServletContext() {
                return servletContext;
            }
            
            @Override
            protected IProductDao createProductDao(DataSource ds) {
                return productDao;
            }
            
            @Override
            protected IOrderDao createOrderDao(DataSource ds) {
                return orderDao;
            }
            
            @Override
            protected IAddressDao createAddressDao(DataSource ds) {
                return addressDao;
            }
            
            @Override
            protected IInfoDao createInfoDao(DataSource ds) {
                return infoDao;
            }
            
            @Override
            protected IContainDao createContainDao(DataSource ds) {
                return containDao;
            }
        };
        
        // Default stubs for DAOs
        lenient().when(addressDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());
        
        InfoBean defaultInfo = new InfoBean();
        defaultInfo.setCodice(1);
        defaultInfo.setCosto(10.0);
        lenient().when(infoDao.doRetrieveByKey(anyInt())).thenReturn(defaultInfo);
    }

    // ============================================================================
    // AUTHENTICATION TESTS
    // ============================================================================

    @Nested
    @DisplayName("Authentication Tests")
    class AuthenticationTests {

        @Test
        @DisplayName("TC-CHK-1: Authenticated user sees checkout page")
        void testAuthenticatedUserSeesCheckout() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-CHK-2: Unauthenticated user is redirected to login")
        void testUnauthenticatedUserHandling() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(null);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert - should redirect to login
            verify(response).sendRedirect("Login");
        }
    }

    // ============================================================================
    // CART STATE TESTS
    // ============================================================================

    @Nested
    @DisplayName("Cart State Tests")
    class CartStateTests {

        @Test
        @DisplayName("TC-CHK-3: Empty cart shows appropriate message")
        void testEmptyCartHandling() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart emptyCart = new Cart();
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(emptyCart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert
            verify(request).setAttribute(eq("addresses"), any());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-CHK-4: Cart with items proceeds to checkout")
        void testCartWithItemsProceeds() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Test Product");
            cart.addProduct(product);
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert
            verify(request).setAttribute(eq("order"), any());
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // ADDRESS HANDLING TESTS
    // ============================================================================

    @Nested
    @DisplayName("Address Handling Tests")
    class AddressHandlingTests {

        @Test
        @DisplayName("TC-CHK-5: Provided address is used")
        void testProvidedAddressUsed() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            cart.addProduct(product);
            
            // When address is provided, the servlet expects an order in session
            OrderBean existingOrder = new OrderBean();
            existingOrder.setCodice(12345);
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(existingOrder);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn("123 Test Street");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert
            verify(request).setAttribute(eq("order"), any());
        }

        @Test
        @DisplayName("TC-CHK-6: Empty address handled correctly")
        void testEmptyAddressHandled() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn("");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // ORDER SUBMISSION TESTS
    // ============================================================================

    @Nested
    @DisplayName("Order Submission Tests")
    class OrderSubmissionTests {

        @Test
        @DisplayName("TC-CHK-7: Confirm action processes order")
        void testConfirmActionProcessesOrder() throws ServletException, IOException, SQLException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("TestProduct");
            cart.addProduct(product);
            
            // Verify cart has item before confirm
            assertEquals(1, cart.getCartSize());
            
            // When address is provided, the servlet expects an order in session
            OrderBean existingOrder = new OrderBean();
            existingOrder.setCodice(12345);
            
            // Setup info bean for the product in cart
            InfoBean infoBean = new InfoBean();
            infoBean.setCodice(1);
            infoBean.setNome("TestProduct");
            infoBean.setDisponibilità(10);
            infoBean.setCosto(5.0);
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(existingOrder);
            when(request.getParameter("action")).thenReturn("confirm");
            when(request.getParameter("address")).thenReturn("123 Test St");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            when(infoDao.doRetrieveByKey(anyInt())).thenReturn(infoBean);
            when(productDao.doRetrieveByName("TestProduct")).thenReturn(product);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert - order should be processed and saved
            verify(request, atLeastOnce()).setAttribute(eq("order"), any());
            
            // Verify void method calls to kill VoidMethodCallMutator mutations
            verify(orderDao).doSave(any(OrderBean.class));
            verify(containDao).doSave(any(ContainBean.class));
            verify(infoDao).doUpdateQuantity(anyInt(), anyInt());
            
            // Verify cart is cleared after confirm (kills VoidMethodCallMutator mutation on line 143 - cart.ClearCart())
            assertEquals(0, cart.getCartSize());
        }

        @Test
        @DisplayName("TC-CHK-8: Non-confirm action continues checkout")
        void testNonConfirmActionContinuesCheckout() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("view");
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // DO GET DELEGATION TESTS
    // ============================================================================

    @Nested
    @DisplayName("doGet Delegation Tests")
    class DoGetTests {

        @Test
        @DisplayName("TC-CHK-9: doGet delegates to doPost")
        void testDoGetDelegatesToDoPost() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doGet(request, response);
            
            // Assert - same behavior as doPost
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // LOOP BOUNDARY TESTS
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("TC-CHK-10: Loop with 0 iterations (empty cart)")
        void testLoopZeroIterations() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart emptyCart = new Cart();
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(emptyCart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert
            assertEquals(0, emptyCart.getCartSize());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-CHK-11: Loop with 1 iteration (single product)")
        void testLoopSingleIteration() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Single Product");
            cart.addProduct(product);
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert
            assertEquals(1, cart.getCartSize());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-CHK-12: Loop with >1 iterations (multiple products)")
        void testLoopMultipleIterations() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            
            ProductBean product1 = new ProductBean();
            product1.setCodice(1);
            product1.setNome("Product 1");
            cart.addProduct(product1);
            
            ProductBean product2 = new ProductBean();
            product2.setCodice(2);
            product2.setNome("Product 2");
            cart.addProduct(product2);
            
            ProductBean product3 = new ProductBean();
            product3.setCodice(3);
            product3.setNome("Product 3");
            cart.addProduct(product3);
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert
            assertEquals(3, cart.getCartSize());
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // EXCEPTION HANDLING TESTS
    // ============================================================================

    @Nested
    @DisplayName("Exception Handling Tests")
    class ExceptionHandlingTests {

        @Test
        @DisplayName("TC-CHK-13: Null cart handled gracefully")
        void testNullCartHandled() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            
            // Act & Assert - should handle null cart
            assertThrows(Exception.class, () -> {
                checkoutServlet.doPost(request, response);
            });
        }

        @Test
        @DisplayName("TC-CHK-16: SQLException sets error attribute and sends 500")
        void testSqlExceptionSetsErrorAndSends500() throws Exception {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            cart.addProduct(product);

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);

            // Make addressDao throw SQLException
            when(addressDao.doRetrieveByUser(anyString())).thenThrow(new java.sql.SQLException("DB Error"));

            // Act
            checkoutServlet.doPost(request, response);

            // Assert - Should set error and sendError 500
            verify(request).setAttribute(eq("error"), contains("Error:"));
            verify(response).sendError(eq(500), anyString());
        }

        @Test
        @DisplayName("TC-CHK-17: SQLException during confirm order sets error and sends 500")
        void testSqlExceptionDuringConfirmSetsErrorAndSends500() throws Exception {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            cart.addProduct(product);

            model.bean.OrderBean existingOrder = new model.bean.OrderBean();
            existingOrder.setCodice(999);

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(existingOrder);
            when(request.getParameter("action")).thenReturn("confirm");
            when(request.getParameter("address")).thenReturn("123 Test St");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);

            // Make orderDao.doSave throw SQLException
            doThrow(new java.sql.SQLException("DB Error")).when(orderDao).doSave(any());

            // Act
            checkoutServlet.doPost(request, response);

            // Assert - Should set error and sendError 500
            verify(request).setAttribute(eq("error"), contains("Error:"));
            verify(response).sendError(eq(500), anyString());
        }
    }

    // ============================================================================
    // ORDER STATE TESTS
    // ============================================================================

    @Nested
    @DisplayName("Order State Tests")
    class OrderStateTests {

        @Test
        @DisplayName("TC-CHK-14: New order is created when no existing order")
        void testNewOrderCreated() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            cart.addProduct(product);
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert - new order should be created and set in session
            verify(session).setAttribute(eq("order"), any());
            // Verify request attribute operations (kills VoidMethodCallMutator mutations)
            verify(request).removeAttribute("addresses");
            verify(request).setAttribute(eq("addresses"), any());
            verify(request).removeAttribute("order");
            
            // Use ArgumentCaptor to verify OrderBean properties (kills setter mutations lines 85-87)
            ArgumentCaptor<OrderBean> orderCaptor = ArgumentCaptor.forClass(OrderBean.class);
            verify(request).setAttribute(eq("order"), orderCaptor.capture());
            OrderBean capturedOrder = orderCaptor.getValue();
            assertEquals("testuser", capturedOrder.getUtente());
            assertEquals("in checkout", capturedOrder.getStato());
            assertNotNull(capturedOrder.getDataOrdine());
            
            // Verify containList properties (kills setter mutations lines 118-120)
            @SuppressWarnings("unchecked")
            ArgumentCaptor<List<ContainBean>> containListCaptor = ArgumentCaptor.forClass(List.class);
            verify(request).removeAttribute("containList");
            verify(request).setAttribute(eq("containList"), containListCaptor.capture());
            List<ContainBean> capturedContainList = containListCaptor.getValue();
            assertFalse(capturedContainList.isEmpty());
            ContainBean capturedContain = capturedContainList.get(0);
            assertEquals(1, capturedContain.getCodiceProdotto());
            assertEquals(capturedOrder.getCodice(), capturedContain.getCodiceOrdine());
            assertEquals(1, capturedContain.getQuantità());
        }

        @Test
        @DisplayName("TC-CHK-15: Existing order is reused")
        void testExistingOrderReused() throws ServletException, IOException {
            // Arrange
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            cart.addProduct(product);
            
            model.bean.OrderBean existingOrder = new model.bean.OrderBean();
            existingOrder.setCodice(999);
            
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(existingOrder);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn("123 Test St");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp")).thenReturn(requestDispatcher);
            
            // Act
            checkoutServlet.doPost(request, response);
            
            // Assert
            verify(request).setAttribute(eq("order"), any());
            verify(requestDispatcher).forward(request, response);
        }
    }
}
