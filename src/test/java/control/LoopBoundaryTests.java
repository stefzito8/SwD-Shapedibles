package control;

import model.Cart;
import model.bean.InfoBean;
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
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Loop Boundary Tests for Controller Layer.
 * 
 * Testing Level: Unit
 * Technique: Loop Boundary Testing (White-Box)
 * 
 * ============================================================================
 * LOOP BOUNDARY TESTING STRATEGY
 * ============================================================================
 * 
 * These tests EXECUTE the actual controller methods (doGet/doPost) to ensure
 * JaCoCo coverage of loop statements. Controllers use factory method seams
 * for DAO creation, which we override to inject mocked DAOs.
 * 
 * For each loop, we test:
 * - 0 iterations: Empty collection/no items
 * - 1 iteration: Single item in collection  
 * - >1 iterations: Multiple items (typically 2-3)
 * 
 * Loop-to-Test Mapping:
 * -----------------------------------------------------------------
 * | Controller      | Loop Location              | Test Methods                    |
 * |-----------------|----------------------------|--------------------------------|
 * | Home            | doPost - product iteration | HomeLoopTests.test*Products    |
 * | Cart            | doPost - cart items        | CartLoopTests.test*CartItems   |
 * | Search          | doGet - search results     | SearchLoopTests.test*Results   |
 * | Checkout        | doPost - order items       | CheckoutLoopTests.test*Items   |
 * | ProductAdmin    | doGet - product list       | ProductAdminLoopTests.test*    |
 * -----------------------------------------------------------------
 * 
 * Note: ProductDetails does NOT contain a collection loop - removed from scope.
 */
@ExtendWith(MockitoExtension.class)
@MockitoSettings(strictness = Strictness.LENIENT)
@DisplayName("Loop Boundary Tests - Executing Real Controller Methods")
public class LoopBoundaryTests {

    // =========================================================================
    // HOME CONTROLLER LOOP TESTS
    // Loop: Iterating over products from ProductDao.doRetrieveAll() in doPost
    // =========================================================================
    
    @Nested
    @DisplayName("Home Controller - Product List Loop (doPost)")
    class HomeLoopTests {
        
        @Mock private HttpServletRequest request;
        @Mock private HttpServletResponse response;
        @Mock private ServletContext servletContext;
        @Mock private RequestDispatcher requestDispatcher;
        @Mock private DataSource dataSource;
        @Mock private IProductDao productDao;
        
        private Home homeServlet;
        
        @BeforeEach
        void setUp() {
            // Create servlet that uses our mocked DAO
            homeServlet = new Home() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
                
                @Override
                protected IProductDao createProductDao(DataSource ds) {
                    return productDao;
                }
            };
            
            lenient().when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
        }
        
        @Test
        @DisplayName("LB-HOME-0: Zero products - loop executes 0 iterations")
        void testZeroProducts() throws ServletException, IOException, SQLException {
            // Arrange - DAO returns empty collection
            Collection<ProductBean> emptyProducts = new ArrayList<>();
            when(productDao.doRetrieveAll(anyString())).thenReturn(emptyProducts);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/home.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            homeServlet.doPost(request, response);
            
            // Assert - Verify products attribute is empty collection
            verify(request).setAttribute(eq("products"), argThat(arg -> {
                if (arg instanceof Collection) {
                    return ((Collection<?>) arg).isEmpty();
                }
                return false;
            }));
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-HOME-1: Single product - loop executes 1 iteration")
        void testSingleProduct() throws ServletException, IOException, SQLException {
            // Arrange - DAO returns single product
            Collection<ProductBean> singleProduct = new ArrayList<>();
            ProductBean p1 = new ProductBean();
            p1.setCodice(1);
            p1.setNome("Product 1");
            singleProduct.add(p1);
            
            when(productDao.doRetrieveAll(anyString())).thenReturn(singleProduct);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/home.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            homeServlet.doPost(request, response);
            
            // Assert - Verify products attribute has 1 item
            verify(request).setAttribute(eq("products"), argThat(arg -> {
                if (arg instanceof Collection) {
                    return ((Collection<?>) arg).size() == 1;
                }
                return false;
            }));
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-HOME-N: Multiple products - loop executes >1 iterations")
        void testMultipleProducts() throws ServletException, IOException, SQLException {
            // Arrange - DAO returns 3 products
            Collection<ProductBean> multipleProducts = new ArrayList<>();
            for (int i = 1; i <= 3; i++) {
                ProductBean p = new ProductBean();
                p.setCodice(i);
                p.setNome("Product " + i);
                multipleProducts.add(p);
            }
            
            when(productDao.doRetrieveAll(anyString())).thenReturn(multipleProducts);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/home.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            homeServlet.doPost(request, response);
            
            // Assert - Verify products attribute has 3 items
            verify(request).setAttribute(eq("products"), argThat(arg -> {
                if (arg instanceof Collection) {
                    return ((Collection<?>) arg).size() == 3;
                }
                return false;
            }));
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-HOME-DOGET: doGet delegates to doPost with same loop behavior")
        void testDoGetDelegatesToDoPost() throws ServletException, IOException, SQLException {
            // Arrange
            Collection<ProductBean> products = new ArrayList<>();
            products.add(new ProductBean());
            products.add(new ProductBean());
            
            when(productDao.doRetrieveAll(anyString())).thenReturn(products);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/home.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute doGet which should delegate to doPost
            homeServlet.doGet(request, response);
            
            // Assert
            verify(request).setAttribute(eq("products"), argThat(arg -> 
                arg instanceof Collection && ((Collection<?>) arg).size() == 2
            ));
            verify(requestDispatcher).forward(request, response);
        }
    }
    
    // =========================================================================
    // CART CONTROLLER LOOP TESTS
    // Loop: Iterating over cart.getProducts() for JSON response
    // =========================================================================
    
    @Nested
    @DisplayName("Cart Controller - Cart Items Loop (doPost)")
    class CartLoopTests {
        
        @Mock private HttpServletRequest request;
        @Mock private HttpServletResponse response;
        @Mock private HttpSession session;
        @Mock private ServletContext servletContext;
        @Mock private RequestDispatcher requestDispatcher;
        @Mock private DataSource dataSource;
        @Mock private IProductDao productDao;
        
        private StringWriter stringWriter;
        private PrintWriter printWriter;
        private control.Cart cartServlet;
        
        @BeforeEach
        void setUp() throws Exception {
            stringWriter = new StringWriter();
            printWriter = new PrintWriter(stringWriter);
            
            cartServlet = new control.Cart() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
                
                @Override
                protected IProductDao createProductDao(DataSource ds) {
                    return productDao;
                }
            };
            
            lenient().when(response.getWriter()).thenReturn(printWriter);
            lenient().when(request.getSession()).thenReturn(session);
            lenient().when(request.getSession(anyBoolean())).thenReturn(session);
            lenient().when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
        }
        
        @Test
        @DisplayName("LB-CART-0: Empty cart - loop executes 0 iterations")
        void testEmptyCart() throws ServletException, IOException {
            // Arrange - Empty cart (0 products to iterate)
            Cart emptyCart = new Cart();
            assertEquals(0, emptyCart.getCartSize(), "Precondition: cart must be empty");
            
            when(session.getAttribute("cart")).thenReturn(emptyCart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            
            // Act - Execute the REAL controller method
            cartServlet.doPost(request, response);
            
            // Assert - JSON response should show cartSize: 0
            printWriter.flush();
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("\"cartSize\":0") || jsonOutput.contains("\"cartSize\": 0"),
                    "Expected cartSize:0 in response, got: " + jsonOutput);
        }
        
        @Test
        @DisplayName("LB-CART-1: Single item - loop executes 1 iteration")
        void testSingleCartItem() throws ServletException, IOException {
            // Arrange - Cart with exactly one item
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Test Product");
            cart.addProduct(product);
            assertEquals(1, cart.getCartSize(), "Precondition: cart must have 1 item");
            
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            
            // Act - Execute the REAL controller method
            cartServlet.doPost(request, response);
            
            // Assert
            printWriter.flush();
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("\"cartSize\":1") || jsonOutput.contains("\"cartSize\": 1"),
                    "Expected cartSize:1 in response, got: " + jsonOutput);
        }
        
        @Test
        @DisplayName("LB-CART-N: Multiple items - loop executes >1 iterations")
        void testMultipleCartItems() throws ServletException, IOException {
            // Arrange - Cart with multiple items (3 different products)
            Cart cart = new Cart();
            for (int i = 1; i <= 3; i++) {
                ProductBean product = new ProductBean();
                product.setCodice(i);
                product.setNome("Product " + i);
                cart.addProduct(product);
            }
            assertEquals(3, cart.getCartSize(), "Precondition: cart must have 3 items");
            
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            
            // Act - Execute the REAL controller method
            cartServlet.doPost(request, response);
            
            // Assert
            printWriter.flush();
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("\"cartSize\":3") || jsonOutput.contains("\"cartSize\": 3"),
                    "Expected cartSize:3 in response, got: " + jsonOutput);
        }
        
        @Test
        @DisplayName("LB-CART-PAGE-0: Empty cart forwards to JSP (non-AJAX)")
        void testEmptyCartForwardsToPage() throws ServletException, IOException {
            // Arrange - Empty cart, non-AJAX request
            Cart emptyCart = new Cart();
            
            when(session.getAttribute("cart")).thenReturn(emptyCart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/cart.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            cartServlet.doPost(request, response);
            
            // Assert
            verify(requestDispatcher).forward(request, response);
        }
    }
    
    // =========================================================================
    // SEARCH CONTROLLER LOOP TESTS
    // Loop: Iterating over search results from ProductDao.searchByName()
    // =========================================================================
    
    @Nested
    @DisplayName("Search Controller - Search Results Loop (doGet)")
    class SearchLoopTests {
        
        @Mock private HttpServletRequest request;
        @Mock private HttpServletResponse response;
        @Mock private HttpSession session;
        @Mock private ServletContext servletContext;
        @Mock private RequestDispatcher requestDispatcher;
        @Mock private DataSource dataSource;
        @Mock private IProductDao productDao;
        @Mock private IInfoDao infoDao;
        
        private StringWriter stringWriter;
        private PrintWriter printWriter;
        private Search searchServlet;
        
        @BeforeEach
        void setUp() throws Exception {
            stringWriter = new StringWriter();
            printWriter = new PrintWriter(stringWriter);
            
            // Create servlet that uses our mocked DAOs
            searchServlet = new Search() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
                
                @Override
                protected IProductDao createProductDao(DataSource ds) {
                    return productDao;
                }
                
                @Override
                protected IInfoDao createInfoDao(DataSource ds) {
                    return infoDao;
                }
            };
            
            lenient().when(response.getWriter()).thenReturn(printWriter);
            lenient().when(request.getSession()).thenReturn(session);
            lenient().when(request.getSession(anyBoolean())).thenReturn(session);
            lenient().when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
        }
        
        @Test
        @DisplayName("LB-SRCH-0: No results - loop executes 0 iterations")
        void testZeroSearchResults() throws ServletException, IOException, SQLException {
            // Arrange - DAO returns empty collection
            Collection<ProductBean> emptyResults = new ArrayList<>();
            when(productDao.searchByName(anyString())).thenReturn(emptyResults);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getParameter("ricerca")).thenReturn("searchterm");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            searchServlet.doGet(request, response);
            
            // Assert - searchResults attribute should be empty collection
            verify(request).setAttribute(eq("searchResults"), argThat(arg -> {
                if (arg instanceof Collection) {
                    return ((Collection<?>) arg).isEmpty();
                }
                return false;
            }));
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-SRCH-1: Single result - loop executes 1 iteration")
        void testSingleSearchResult() throws ServletException, IOException, SQLException {
            // Arrange - DAO returns single product
            Collection<ProductBean> singleResult = new ArrayList<>();
            ProductBean p1 = new ProductBean();
            p1.setCodice(1);
            p1.setNome("Found Product");
            singleResult.add(p1);
            
            when(productDao.searchByName(anyString())).thenReturn(singleResult);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getParameter("ricerca")).thenReturn("searchterm");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            searchServlet.doGet(request, response);
            
            // Assert - searchResults should have exactly 1 item
            verify(request).setAttribute(eq("searchResults"), argThat(arg -> {
                if (arg instanceof Collection) {
                    return ((Collection<?>) arg).size() == 1;
                }
                return false;
            }));
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-SRCH-N: Multiple results - loop executes >1 iterations")
        void testMultipleSearchResults() throws ServletException, IOException, SQLException {
            // Arrange - DAO returns multiple products
            Collection<ProductBean> multipleResults = new ArrayList<>();
            for (int i = 1; i <= 5; i++) {
                ProductBean p = new ProductBean();
                p.setCodice(i);
                p.setNome("Product " + i);
                multipleResults.add(p);
            }
            
            when(productDao.searchByName(anyString())).thenReturn(multipleResults);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getParameter("ricerca")).thenReturn("searchterm");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            searchServlet.doGet(request, response);
            
            // Assert - searchResults should have 5 items
            verify(request).setAttribute(eq("searchResults"), argThat(arg -> {
                if (arg instanceof Collection) {
                    return ((Collection<?>) arg).size() == 5;
                }
                return false;
            }));
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-SRCH-AJAX-0: AJAX with no results returns empty JSON array")
        void testAjaxZeroResults() throws ServletException, IOException, SQLException {
            // Arrange - DAO returns empty collection, AJAX request
            Collection<ProductBean> emptyResults = new ArrayList<>();
            when(productDao.searchByName(anyString())).thenReturn(emptyResults);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getParameter("ricerca")).thenReturn("searchterm");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            
            // Act - Execute the REAL controller method
            searchServlet.doGet(request, response);
            
            // Assert - JSON response should be empty array
            verify(response).setContentType("application/json");
            printWriter.flush();
            String jsonOutput = stringWriter.toString();
            assertEquals("[]", jsonOutput.trim(), "Expected empty JSON array for 0 results");
        }
        
        @Test
        @DisplayName("LB-SRCH-AJAX-N: AJAX with multiple results returns JSON array")
        void testAjaxMultipleResults() throws ServletException, IOException, SQLException {
            // Arrange - DAO returns multiple products, AJAX request
            Collection<ProductBean> multipleResults = new ArrayList<>();
            for (int i = 1; i <= 3; i++) {
                ProductBean p = new ProductBean();
                p.setCodice(i);
                p.setNome("Product" + i);
                multipleResults.add(p);
            }
            
            when(productDao.searchByName(anyString())).thenReturn(multipleResults);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getParameter("ricerca")).thenReturn("searchterm");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            
            // Act - Execute the REAL controller method
            searchServlet.doGet(request, response);
            
            // Assert - JSON response should contain items
            verify(response).setContentType("application/json");
            printWriter.flush();
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.startsWith("[") && jsonOutput.endsWith("]"), 
                    "Expected JSON array, got: " + jsonOutput);
            // Verify it contains product data
            assertTrue(jsonOutput.contains("\"codice\""), 
                    "Expected codice in JSON, got: " + jsonOutput);
        }
        
        @Test
        @DisplayName("LB-SRCH-DOPOST: doPost delegates to doGet with same loop behavior")
        void testDoPostDelegatesToDoGet() throws ServletException, IOException, SQLException {
            // Arrange
            Collection<ProductBean> results = new ArrayList<>();
            results.add(new ProductBean());
            results.add(new ProductBean());
            
            when(productDao.searchByName(anyString())).thenReturn(results);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getParameter("ricerca")).thenReturn("test");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute doPost which should delegate to doGet
            searchServlet.doPost(request, response);
            
            // Assert
            verify(request).setAttribute(eq("searchResults"), argThat(arg -> 
                arg instanceof Collection && ((Collection<?>) arg).size() == 2
            ));
            verify(requestDispatcher).forward(request, response);
        }
    }
    
    // =========================================================================
    // CHECKOUT CONTROLLER LOOP TESTS
    // Loop: Iterating over cart items for order processing
    // =========================================================================
    
    @Nested
    @DisplayName("Checkout Controller - Order Items Loop (doPost)")
    class CheckoutLoopTests {
        
        @Mock private HttpServletRequest request;
        @Mock private HttpServletResponse response;
        @Mock private HttpSession session;
        @Mock private ServletContext servletContext;
        @Mock private RequestDispatcher requestDispatcher;
        @Mock private DataSource dataSource;
        @Mock private IProductDao productDao;
        @Mock private IOrderDao orderDao;
        @Mock private IAddressDao addressDao;
        @Mock private IInfoDao infoDao;
        @Mock private IContainDao containDao;
        
        private Checkout checkoutServlet;
        
        @BeforeEach
        void setUp() throws SQLException {
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
            
            lenient().when(request.getSession()).thenReturn(session);
            lenient().when(request.getSession(anyBoolean())).thenReturn(session);
            lenient().when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            
            // Default stubs for DAOs
            lenient().when(addressDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());
            
            InfoBean defaultInfo = new InfoBean();
            defaultInfo.setCodice(1);
            defaultInfo.setCosto(10.0);
            lenient().when(infoDao.doRetrieveByKey(anyInt())).thenReturn(defaultInfo);
        }
        
        @Test
        @DisplayName("LB-CHK-0: Empty cart - loop executes 0 iterations")
        void testEmptyCartCheckout() throws ServletException, IOException {
            // Arrange - Empty cart (0 items to process)
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart emptyCart = new Cart();
            assertEquals(0, emptyCart.getCartSize(), "Precondition: cart must be empty");
            
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(emptyCart);
            when(session.getAttribute("order")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            checkoutServlet.doPost(request, response);
            
            // Assert
            assertEquals(0, emptyCart.getCartSize());
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-CHK-1: Single item - loop executes 1 iteration")
        void testSingleItemCheckout() throws ServletException, IOException {
            // Arrange - Cart with exactly 1 item
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Single Product");
            cart.addProduct(product);
            assertEquals(1, cart.getCartSize(), "Precondition: cart must have 1 item");
            
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            checkoutServlet.doPost(request, response);
            
            // Assert
            assertEquals(1, cart.getCartSize());
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-CHK-N: Multiple items - loop executes >1 iterations")
        void testMultipleItemsCheckout() throws ServletException, IOException {
            // Arrange - Cart with multiple items
            UserBean user = new UserBean();
            user.setUsername("testuser");
            Cart cart = new Cart();
            for (int i = 1; i <= 3; i++) {
                ProductBean p = new ProductBean();
                p.setCodice(i);
                p.setNome("Product " + i);
                cart.addProduct(p);
            }
            assertEquals(3, cart.getCartSize(), "Precondition: cart must have 3 items");
            
            when(session.getAttribute("LoggedUser")).thenReturn(user);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(session.getAttribute("order")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("address")).thenReturn(null);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            checkoutServlet.doPost(request, response);
            
            // Assert
            assertEquals(3, cart.getCartSize());
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-CHK-UNAUTH: Unauthenticated user redirects to login")
        void testUnauthenticatedCheckout() throws ServletException, IOException {
            // Arrange - No logged in user
            when(session.getAttribute("LoggedUser")).thenReturn(null);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            
            // Act - Execute the REAL controller method
            checkoutServlet.doPost(request, response);
            
            // Assert - Should redirect to login
            verify(response).sendRedirect(contains("Login"));
        }
    }
    
    // =========================================================================
    // PRODUCT ADMIN CONTROLLER LOOP TESTS
    // Loop: Iterating over products from ProductDao.doRetrieveAll()
    // =========================================================================
    
    @Nested
    @DisplayName("ProductAdmin Controller - Product List Loop (doGet)")
    class ProductAdminLoopTests {
        
        @Mock private HttpServletRequest request;
        @Mock private HttpServletResponse response;
        @Mock private HttpSession session;
        @Mock private ServletContext servletContext;
        @Mock private RequestDispatcher requestDispatcher;
        @Mock private DataSource dataSource;
        @Mock private IProductDao productDao;
        
        private ProductAdmin productAdminServlet;
        
        @BeforeEach
        void setUp() {
            // Create servlet that uses our mocked DAO
            productAdminServlet = new ProductAdmin() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
                
                @Override
                protected IProductDao createProductDao(DataSource ds) {
                    return productDao;
                }
            };
            
            lenient().when(request.getSession()).thenReturn(session);
            lenient().when(request.getSession(anyBoolean())).thenReturn(session);
            lenient().when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
        }
        
        @Test
        @DisplayName("LB-PADMIN-0: Zero products - loop executes 0 iterations")
        void testZeroProducts() throws ServletException, IOException, SQLException {
            // Arrange - DAO returns empty collection
            Collection<ProductBean> emptyProducts = new ArrayList<>();
            when(productDao.doRetrieveAll(any())).thenReturn(emptyProducts);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            productAdminServlet.doGet(request, response);
            
            // Assert - products attribute should be empty collection
            verify(request).setAttribute(eq("products"), argThat(arg -> {
                if (arg instanceof Collection) {
                    return ((Collection<?>) arg).isEmpty();
                }
                return false;
            }));
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-PADMIN-1: Single product - loop executes 1 iteration")
        void testSingleProduct() throws ServletException, IOException, SQLException {
            // Arrange - DAO returns single product
            Collection<ProductBean> singleProduct = new ArrayList<>();
            ProductBean p1 = new ProductBean();
            p1.setCodice(1);
            p1.setNome("Product 1");
            singleProduct.add(p1);
            
            when(productDao.doRetrieveAll(any())).thenReturn(singleProduct);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            productAdminServlet.doGet(request, response);
            
            // Assert - products attribute should have 1 item
            verify(request).setAttribute(eq("products"), argThat(arg -> {
                if (arg instanceof Collection) {
                    return ((Collection<?>) arg).size() == 1;
                }
                return false;
            }));
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-PADMIN-N: Multiple products - loop executes >1 iterations")
        void testMultipleProducts() throws ServletException, IOException, SQLException {
            // Arrange - DAO returns multiple products
            Collection<ProductBean> multipleProducts = new ArrayList<>();
            for (int i = 1; i <= 4; i++) {
                ProductBean p = new ProductBean();
                p.setCodice(i);
                p.setNome("Product " + i);
                multipleProducts.add(p);
            }
            
            when(productDao.doRetrieveAll(any())).thenReturn(multipleProducts);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute the REAL controller method
            productAdminServlet.doGet(request, response);
            
            // Assert - products attribute should have 4 items
            verify(request).setAttribute(eq("products"), argThat(arg -> {
                if (arg instanceof Collection) {
                    return ((Collection<?>) arg).size() == 4;
                }
                return false;
            }));
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("LB-PADMIN-DOPOST: doPost delegates to doGet with same loop behavior")
        void testDoPostDelegatesToDoGet() throws ServletException, IOException, SQLException {
            // Arrange
            Collection<ProductBean> products = new ArrayList<>();
            products.add(new ProductBean());
            products.add(new ProductBean());
            
            when(productDao.doRetrieveAll(any())).thenReturn(products);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);
            
            // Act - Execute doPost which should delegate to doGet
            productAdminServlet.doPost(request, response);
            
            // Assert
            verify(request).setAttribute(eq("products"), argThat(arg -> 
                arg instanceof Collection && ((Collection<?>) arg).size() == 2
            ));
            verify(requestDispatcher).forward(request, response);
        }
    }
    
    // Note: ProductDetails does NOT contain a collection loop - removed from scope.
}
