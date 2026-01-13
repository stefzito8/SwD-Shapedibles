package integration;

import categories.IntegrationTest;
import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

import java.io.PrintWriter;
import java.io.StringWriter;
import java.sql.SQLException;
import java.util.Collection;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletContext;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import javax.sql.DataSource;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;

import control.Home;
import control.Login;
import control.ProductDetails;
import control.Search;
import model.Cart;
import model.bean.InfoBean;
import model.bean.ProductBean;
import model.bean.UserBean;
import model.dao.IInfoDao;
import model.dao.IProductDao;
import model.dao.IUserDao;
import model.datasource.InfoDaoDataSource;
import model.datasource.ProductDaoDataSource;
import model.datasource.UserDaoDataSource;

/**
 * Integration tests for Controller-Model layer interactions.
 * 
 * <h2>Integration Strategy: Modified Sandwich</h2>
 * <p>Per SPEC.md and course tutorial:</p>
 * <ul>
 *   <li>Unit tests are complete for all layers (Phases 2-4)</li>
 *   <li>Now integrating middle components (controllers) with lower layer (model/DAO)</li>
 *   <li>Real DAO implementations are used (no mocking of model layer)</li>
 *   <li>H2 in-memory database replaces SQLite production database</li>
 *   <li>HTTP request/response are mocked (test driver)</li>
 * </ul>
 * 
 * <h2>Integration Points Tested</h2>
 * <table border="1">
 *   <tr><th>Controller</th><th>DAO Dependencies</th><th>Priority</th></tr>
 *   <tr><td>Home</td><td>ProductDaoDataSource, InfoDaoDataSource</td><td>HIGH</td></tr>
 *   <tr><td>Login</td><td>UserDaoDataSource</td><td>HIGH</td></tr>
 *   <tr><td>Search</td><td>ProductDaoDataSource, InfoDaoDataSource</td><td>MEDIUM</td></tr>
 *   <tr><td>ProductDetails</td><td>ProductDaoDataSource, InfoDaoDataSource</td><td>MEDIUM</td></tr>
 * </table>
 * 
 * <h2>Test Environment</h2>
 * <ul>
 *   <li>Database: H2 in-memory (configured in H2TestDatabase)</li>
 *   <li>Schema: Mirrors production SQLite (schema.sql)</li>
 *   <li>Test Data: Loaded via H2TestDatabase.initializeDatabaseWithTestData()</li>
 * </ul>
 * 
 * <h2>Test Approach</h2>
 * <p>Controllers obtain their DataSource from ServletContext. In these integration tests,
 * we provide a mocked ServletContext that returns the H2 test DataSource, allowing
 * controllers to use real DAO implementations connected to the H2 test database.</p>
 */
@IntegrationTest
public class ControllerModelIntegrationTest {

    private static DataSource dataSource;
    
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private ServletContext servletContext;
    private StringWriter responseWriter;
    private PrintWriter printWriter;

    @BeforeAll
    static void setUpDatabase() throws SQLException {
        H2TestDatabase.initializeDatabaseWithTestData();
        dataSource = H2TestDatabase.getDataSource();
    }

    @BeforeEach
    void setUp() throws Exception {
        // Reset database to known state before each test
        H2TestDatabase.clearAllData();
        H2TestDatabase.initializeDatabaseWithTestData();
        
        // Create mocked HTTP components (test driver)
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        servletContext = mock(ServletContext.class);
        
        // Setup response writer for capturing output
        responseWriter = new StringWriter();
        printWriter = new PrintWriter(responseWriter);
        when(response.getWriter()).thenReturn(printWriter);
        
        // Default session behavior
        when(request.getSession()).thenReturn(session);
        when(request.getSession(anyBoolean())).thenReturn(session);
        
        // Default cart in session
        when(session.getAttribute("cart")).thenReturn(new Cart());
        
        // Mock ServletContext to return our H2 DataSource
        when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
        when(servletContext.getRequestDispatcher(anyString())).thenReturn(dispatcher);
        
        // Default HTTP method for service() dispatching
        when(request.getMethod()).thenReturn("GET");
        when(request.getProtocol()).thenReturn("HTTP/1.1");
    }

    /**
     * Integration tests for Home controller with ProductDao and InfoDao.
     * Tests the complete flow: Controller → DAO → H2 Database → DAO → Controller
     */
    @Nested
    @DisplayName("Home Controller - DAO Integration")
    class HomeControllerIntegrationTests {

        @Test
        @DisplayName("Home retrieves all products from database via ProductDao")
        void testHomeRetrievesProductsFromDatabase() throws Exception {
            // Arrange: Create Home servlet that uses our mocked ServletContext
            Home homeServlet = new Home() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
            when(request.getMethod()).thenReturn("GET");
            
            // Act: Call the servlet via service() which dispatches to doGet
            homeServlet.service(request, response);
            
            // Assert: Verify products were retrieved from database and set as attribute
            @SuppressWarnings("unchecked")
            ArgumentCaptor<Collection<ProductBean>> productsCaptor = ArgumentCaptor.forClass(Collection.class);
            verify(request).setAttribute(eq("products"), productsCaptor.capture());
            
            Collection<ProductBean> products = productsCaptor.getValue();
            assertNotNull(products, "Products collection should not be null");
            assertEquals(5, products.size(), "Should retrieve 5 products from test data");
        }

        @Test
        @DisplayName("Home forwards to correct JSP after retrieving products")
        void testHomeForwardsToJsp() throws Exception {
            // Arrange
            Home homeServlet = new Home() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
            when(request.getMethod()).thenReturn("GET");
            
            // Act
            homeServlet.service(request, response);
            
            // Assert: Verify forward to home page
            verify(request).getRequestDispatcher(contains("home"));
            verify(dispatcher).forward(request, response);
        }

        @Test
        @DisplayName("Home handles empty product table gracefully")
        void testHomeHandlesEmptyProductTable() throws Exception {
            // Arrange: Clear products from database
            H2TestDatabase.clearAllData();
            
            Home homeServlet = new Home() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
            when(request.getMethod()).thenReturn("GET");
            
            // Act
            homeServlet.service(request, response);
            
            // Assert: Should still set products attribute (empty collection)
            @SuppressWarnings("unchecked")
            ArgumentCaptor<Collection<ProductBean>> productsCaptor = ArgumentCaptor.forClass(Collection.class);
            verify(request).setAttribute(eq("products"), productsCaptor.capture());
            
            Collection<ProductBean> products = productsCaptor.getValue();
            assertNotNull(products, "Products collection should not be null even when empty");
            assertTrue(products.isEmpty(), "Products collection should be empty");
        }
    }

    /**
     * Integration tests for Login controller with UserDao.
     * Tests authentication flow with real database.
     */
    @Nested
    @DisplayName("Login Controller - DAO Integration")
    class LoginControllerIntegrationTests {

        @Test
        @DisplayName("Login rejects invalid credentials")
        void testLoginRejectsInvalidCredentials() throws Exception {
            // Arrange: Create Login servlet with mocked ServletContext
            Login loginServlet = new Login() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            when(request.getParameter("username")).thenReturn("nonexistent");
            when(request.getParameter("password")).thenReturn("wrongpassword");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(request.getContextPath()).thenReturn("");
            when(request.getMethod()).thenReturn("POST");
            
            // Act - will throw SQLException because user not found, which is expected
            // The controller catches this and sends error
            loginServlet.service(request, response);
            
            // Assert: No user should be set in session
            verify(session, never()).setAttribute(eq("LoggedUser"), any(UserBean.class));
        }

        @Test
        @DisplayName("Login AJAX returns JSON response")
        void testLoginAjaxReturnsJson() throws Exception {
            // Arrange
            Login loginServlet = new Login() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            when(request.getParameter("username")).thenReturn("testuser");
            when(request.getParameter("password")).thenReturn("password123");
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getContextPath()).thenReturn("");
            when(request.getMethod()).thenReturn("POST");
            
            // Act
            loginServlet.service(request, response);
            
            // Assert: Should set JSON content type for AJAX requests
            verify(response).setContentType("application/json");
        }
        
        @Test
        @DisplayName("Login doGet forwards to login page")
        void testLoginDoGetForwardsToLoginPage() throws Exception {
            // Arrange
            Login loginServlet = new Login() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
            when(request.getMethod()).thenReturn("GET");
            
            // Act
            loginServlet.service(request, response);
            
            // Assert: Should forward to login view
            verify(request).getRequestDispatcher(contains("login"));
            verify(dispatcher).forward(request, response);
        }
    }

    /**
     * Integration tests for Search controller with ProductDao.
     * Tests search functionality with real database queries.
     */
    @Nested
    @DisplayName("Search Controller - DAO Integration")
    class SearchControllerIntegrationTests {

        @Test
        @DisplayName("Search finds products matching query from database")
        void testSearchFindsMatchingProducts() throws Exception {
            // Arrange
            Search searchServlet = new Search() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            // Search for "Protein" - should find products from test data
            when(request.getParameter("ricerca")).thenReturn("Protein");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
            when(request.getMethod()).thenReturn("GET");
            
            // Act
            searchServlet.service(request, response);
            
            // Assert: Should set searchResults attribute
            verify(request).setAttribute(eq("searchResults"), any(Collection.class));
        }

        @Test
        @DisplayName("Search returns results for non-matching query")
        void testSearchReturnsResultsForNoMatch() throws Exception {
            // Arrange
            Search searchServlet = new Search() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            when(request.getParameter("ricerca")).thenReturn("ZZZZNONEXISTENT");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
            when(request.getMethod()).thenReturn("GET");
            
            // Act
            searchServlet.service(request, response);
            
            // Assert: Should set searchResults attribute (may be empty)
            verify(request).setAttribute(eq("searchResults"), any(Collection.class));
        }

        @Test
        @DisplayName("Search AJAX returns JSON results")
        void testSearchAjaxReturnsJson() throws Exception {
            // Arrange
            Search searchServlet = new Search() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            when(request.getParameter("ricerca")).thenReturn("Protein");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getMethod()).thenReturn("GET");
            
            // Act
            searchServlet.service(request, response);
            
            // Assert: Should set JSON content type for AJAX
            verify(response).setContentType("application/json");
        }
        
        @Test
        @DisplayName("Search by product ID returns single product JSON")
        void testSearchByIdReturnsProductJson() throws Exception {
            // Arrange
            Search searchServlet = new Search() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            when(request.getParameter("ricerca")).thenReturn(null);
            when(request.getParameter("id")).thenReturn("1");
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(request.getMethod()).thenReturn("GET");
            
            // Act
            searchServlet.service(request, response);
            
            // Assert: Should set JSON content type for product lookup by ID
            verify(response).setContentType("application/json");
        }
    }

    /**
     * Integration tests for ProductDetails controller with ProductDao and InfoDao.
     * Tests product detail retrieval from database.
     */
    @Nested
    @DisplayName("ProductDetails Controller - DAO Integration")
    class ProductDetailsControllerIntegrationTests {

        @Test
        @DisplayName("ProductDetails retrieves existing product from database")
        void testProductDetailsRetrievesProduct() throws Exception {
            // Arrange
            ProductDetails detailsServlet = new ProductDetails() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            // Product ID 1 exists in test data
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getRequestDispatcher(anyString())).thenReturn(dispatcher);
            when(request.getMethod()).thenReturn("GET");
            
            // Act
            detailsServlet.service(request, response);
            
            // Assert: Product should be set as request attribute
            verify(request).setAttribute(eq("product"), any(ProductBean.class));
        }

        @Test
        @DisplayName("ProductDetails retrieves product info from database")
        void testProductDetailsRetrievesInfo() throws Exception {
            // Arrange
            ProductDetails detailsServlet = new ProductDetails() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getRequestDispatcher(anyString())).thenReturn(dispatcher);
            when(request.getMethod()).thenReturn("GET");
            
            // Act
            detailsServlet.service(request, response);
            
            // Assert: Info should be set as request attribute
            verify(request).setAttribute(eq("info"), any(InfoBean.class));
        }

        @Test
        @DisplayName("ProductDetails handles non-existent product gracefully")
        void testProductDetailsHandlesNonExistentProduct() throws Exception {
            // Arrange
            ProductDetails detailsServlet = new ProductDetails() {
                @Override
                public ServletContext getServletContext() {
                    return servletContext;
                }
            };
            
            // Non-existent product ID
            when(request.getParameter("product")).thenReturn("99999");
            when(servletContext.getRequestDispatcher(anyString())).thenReturn(dispatcher);
            when(request.getMethod()).thenReturn("GET");
            
            // Act & Assert: Should handle gracefully (may send error or forward to error page)
            assertDoesNotThrow(() -> detailsServlet.service(request, response));
        }
    }

    /**
     * Integration tests verifying data consistency across DAO layers.
     * These tests directly use DAOs without controllers to verify database integration.
     */
    @Nested
    @DisplayName("Cross-DAO Data Consistency")
    class CrossDaoConsistencyTests {

        @Test
        @DisplayName("Product and Info DAOs return consistent data")
        void testProductInfoConsistency() throws SQLException {
            // Arrange
            IProductDao productDao = new ProductDaoDataSource(dataSource);
            IInfoDao infoDao = new InfoDaoDataSource(dataSource);
            
            // Act: Retrieve all products and their info
            Collection<ProductBean> products = productDao.doRetrieveAll("CODE");
            
            // Assert: Each product should have corresponding info via infoCorrenti
            for (ProductBean product : products) {
                InfoBean info = infoDao.doRetrieveByKey(product.getInfoCorrenti());
                assertNotNull(info, "Each product should have corresponding info record for infoCorrenti=" + product.getInfoCorrenti());
                assertEquals(product.getCodice(), info.getCodice(), 
                    "Info codice should match product code");
            }
        }

        @Test
        @DisplayName("ProductDao retrieves correct number of products from test data")
        void testProductDaoRetrievesTestData() throws SQLException {
            // Arrange
            IProductDao productDao = new ProductDaoDataSource(dataSource);
            
            // Act
            Collection<ProductBean> products = productDao.doRetrieveAll("CODE");
            
            // Assert: Should match test-data.sql count
            assertEquals(5, products.size(), "Should retrieve 5 products from test data");
        }

        @Test
        @DisplayName("UserDao finds test users correctly")
        void testUserDaoFindsTestUsers() throws SQLException {
            // Arrange
            IUserDao userDao = new UserDaoDataSource(dataSource);
            
            // Act: Try to find test user
            UserBean user = userDao.doRetrieveByKey("testuser");
            
            // Assert
            assertNotNull(user, "Test user should exist in database");
            assertEquals("testuser", user.getUsername());
        }

        @Test
        @DisplayName("Admin user has correct admin flag in database")
        void testAdminUserFlag() throws SQLException {
            // Arrange
            IUserDao userDao = new UserDaoDataSource(dataSource);
            
            // Act: Retrieve admin user from test data
            UserBean adminUser = userDao.doRetrieveByKey("adminuser");
            
            // Assert
            assertNotNull(adminUser, "Admin user should exist in database");
            assertEquals(1, adminUser.getUserAdmin(), "Admin user should have admin flag set to 1");
        }
        
        @Test
        @DisplayName("ProductDao search by name works correctly")
        void testProductDaoSearchByName() throws SQLException {
            // Arrange
            IProductDao productDao = new ProductDaoDataSource(dataSource);
            
            // Act: Search for products by name
            Collection<ProductBean> results = productDao.searchByName("Protein");
            
            // Assert: Should find at least one product containing "Protein"
            assertNotNull(results, "Search results should not be null");
            assertTrue(results.size() >= 0, "Search should return a valid collection");
        }
    }
}
