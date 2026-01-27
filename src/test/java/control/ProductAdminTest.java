package control;

import categories.UnitTest;
import model.Cart;
import model.bean.ProductBean;
import model.bean.UserBean;
import model.dao.IProductDao;
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
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;
import org.mockito.junit.jupiter.MockitoSettings;
import org.mockito.quality.Strictness;

/**
 * Unit tests for ProductAdmin controller.
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
 * | PA-B1     | cart == null                 | Create new cart   | Use existing   |
 * | PA-B2     | action != null               | Process action    | Skip action    |
 * | PA-B3     | action == "addC"             | Add to cart       | Check next     |
 * | PA-B4     | action == "read"             | Show product      | Check next     |
 * | PA-B5     | action == "delete"           | Delete product    | No action      |
 * | PA-B6     | SQLException (first catch)   | Error + sendError | Normal flow    |
 * | PA-B7     | SQLException (second catch)  | Error + sendError | Normal flow    |
 * -----------------------------------------------------------------
 * 
 * Method: doPost(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | PA-B8     | Delegates to doGet           | doGet called      | N/A            |
 * -----------------------------------------------------------------
 * 
 * ============================================================================
 * TEST CASE DESIGN (Step 3.2)
 * ============================================================================
 * 
 * Session/Cart Handling Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-PA-1      | B1=true       | Cart is null                 | New cart created     |
 * | TC-PA-2      | B1=false      | Cart exists                  | Existing cart used   |
 * 
 * Action Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-PA-3      | B2=false      | No action parameter          | Skip action handling |
 * | TC-PA-4      | B3=true       | action="addC"                | Product added to cart|
 * | TC-PA-5      | B4=true       | action="read"                | Product details shown|
 * | TC-PA-6      | B5=true       | action="delete"              | Product deleted      |
 * | TC-PA-7      | B2=true       | action="invalid"             | No matching action   |
 * 
 * Exception Handling Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-PA-8      | B6=true       | SQLException in action       | Error response 500   |
 * | TC-PA-9      | B7=true       | SQLException in retrieve     | Error response 500   |
 * 
 * doPost Delegation Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-PA-10     | B8            | POST request                 | doGet called         |
 * 
 * Product Listing Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-PA-11     | Normal flow   | No sort parameter            | Products unsorted    |
 * | TC-PA-12     | Normal flow   | sort="codice"                | Products by code     |
 * | TC-PA-13     | Normal flow   | sort="nome"                  | Products by name     |
 * | TC-PA-14     | Normal flow   | sort="descrizione"            | Products by desc     |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets:
 * - TER1 (Statement): ≥ 80%
 * - TER2 (Branch): ≥ 70%
 * 
 * @see control.ProductAdmin
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@MockitoSettings(strictness = Strictness.LENIENT)
@DisplayName("ProductAdmin Controller Unit Tests")
public class ProductAdminTest {

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
    private IProductDao productDao;

    private ProductAdmin productAdminServlet;

    @BeforeEach
    void setUp() throws Exception {
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
    }

    // ============================================================================
    // SESSION/CART HANDLING TESTS
    // ============================================================================

    @Nested
    @DisplayName("Session/Cart Handling Tests")
    class SessionCartHandlingTests {

        @Test
        @DisplayName("TC-PA-1: New cart created when session cart is null - verifies setAttribute is called")
        void testNewCartCreatedWhenNull() throws ServletException, IOException, java.sql.SQLException {
            // Arrange
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert - cart setAttribute is called at least twice (once when created, once after processing)
            // This kills the mutation on line 44 by verifying the setAttribute call occurs
            org.mockito.ArgumentCaptor<Cart> cartCaptor = org.mockito.ArgumentCaptor.forClass(Cart.class);
            verify(session, atLeast(2)).setAttribute(eq("cart"), cartCaptor.capture());
            
            // Verify the captured cart is not null
            assertNotNull(cartCaptor.getValue());
            assertTrue(cartCaptor.getValue() instanceof Cart);
        }

        @Test
        @DisplayName("TC-PA-2: Existing cart reused from session")
        void testExistingCartReused() throws ServletException, IOException {
            // Arrange
            Cart existingCart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            existingCart.addProduct(product);

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(existingCart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert - existing cart should be set back to session
            verify(session).setAttribute("cart", existingCart);
        }
    }

    // ============================================================================
    // ACTION TESTS
    // ============================================================================

    @Nested
    @DisplayName("Action Tests")
    class ActionTests {

        @Test
        @DisplayName("TC-PA-3: No action parameter skips action handling")
        void testNoActionParameter() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert - should forward to admin page without processing any action
            verify(requestDispatcher).forward(request, response);
            verify(request, never()).getParameter("id");
        }

        @Test
        @DisplayName("TC-PA-4: addC action adds product to cart - verifies product is actually added")
        void testAddCActionAddsProductToCart() throws ServletException, IOException, java.sql.SQLException {
            // Arrange
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Test Product");

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("addC");
            when(request.getParameter("id")).thenReturn("1");
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);
            when(productDao.doRetrieveByKey(1)).thenReturn(product);

            // Assert cart is initially empty
            assertEquals(0, cart.getCartSize());

            // Act
            productAdminServlet.doGet(request, response);

            // Assert - verify addProduct was called by checking cart now has product
            assertEquals(1, cart.getCartSize());
            assertTrue(cart.getProducts().contains(product));
            verify(productDao).doRetrieveByKey(1);
            verify(session).setAttribute(eq("cart"), eq(cart));
        }
        
        @Test
        @DisplayName("addC action - verify product retrieval is used")
        void testAddCActionRetrievesAndAddsProduct() throws ServletException, IOException, java.sql.SQLException {
            // Arrange
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(99);
            product.setNome("Specific Product");

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("addC");
            when(request.getParameter("id")).thenReturn("99");
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);
            when(productDao.doRetrieveByKey(99)).thenReturn(product);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert - cart must contain the specific product (kills mutation if addProduct call is removed)
            assertTrue(cart.getProducts().contains(product), "Cart should contain the added product");
            assertEquals(1, cart.getProductQuantity(product), "Product quantity should be 1");
        }

        @Test
        @DisplayName("TC-PA-5: read action - verifies removeAttribute before setAttribute for product")
        void testReadActionShowsProductDetails() throws ServletException, IOException, java.sql.SQLException {
            // Arrange
            Cart cart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Test Product");

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("read");
            when(request.getParameter("id")).thenReturn("1");
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);
            when(productDao.doRetrieveByKey(1)).thenReturn(product);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert - verify removeAttribute is called BEFORE setAttribute (kills removeAttribute mutation)
            org.mockito.InOrder inOrder = inOrder(request);
            inOrder.verify(request).removeAttribute("product");
            inOrder.verify(request).setAttribute("product", product);
            verify(productDao).doRetrieveByKey(1);
        }

        @Test
        @DisplayName("TC-PA-6: delete action deletes product")
        void testDeleteActionDeletesProduct() throws ServletException, IOException, SQLException {
            // Arrange
            Cart cart = new Cart();

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("delete");
            when(request.getParameter("id")).thenReturn("1");
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert - delete action should be processed and doDelete called
            verify(request).getParameter("id");
            verify(productDao).doDelete(1);
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-PA-7: Invalid action results in no matching action")
        void testInvalidActionNoMatch() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("invalidAction");
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert - should still forward to admin page
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
        @DisplayName("TC-PA-8: SQLException in action handling - sets error and sends 500")
        void testSqlExceptionInActionHandling() throws Exception {
            // Arrange
            Cart cart = new Cart();
            java.sql.SQLException sqlException = new java.sql.SQLException("Product action error");

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("addC");
            when(request.getParameter("id")).thenReturn("1");
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);
            when(productDao.doRetrieveByKey(1)).thenThrow(sqlException);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert - Kill mutations by verifying BOTH setAttribute and sendError
            verify(request).setAttribute(eq("error"), 
                eq("Error: sembra esserci un problema con l'elaborazione dei prodotti."));
            verify(response).sendError(eq(500), argThat(msg -> 
                msg != null && msg.contains("Product action error")
            ));
        }

        @Test
        @DisplayName("TC-PA-9: SQLException during product retrieval - sets error and sends 500")
        void testSqlExceptionDuringProductRetrieval() throws Exception {
            // Arrange
            Cart cart = new Cart();
            java.sql.SQLException sqlException = new java.sql.SQLException("Product retrieval error");

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);
            when(productDao.doRetrieveAll(any())).thenThrow(sqlException);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert - Kill mutations by verifying specific error message
            verify(request).setAttribute(eq("error"), 
                eq("Error: c'è stato un problema con il recupero dati dei prodotti."));
            verify(response).sendError(eq(500), contains("Product retrieval error"));
        }

        @Test
        @DisplayName("TC-PA-9b: SQLException verifies error flow order")
        void testSqlExceptionFlowOrder() throws Exception {
            // Arrange
            Cart cart = new Cart();
            java.sql.SQLException sqlException = new java.sql.SQLException("Flow error");

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);
            when(productDao.doRetrieveAll(any())).thenThrow(sqlException);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert - Use InOrder to verify sequence
            org.mockito.InOrder inOrder = inOrder(request, response);
            inOrder.verify(request).setAttribute(eq("error"), anyString());
            inOrder.verify(response).sendError(eq(500), anyString());
        }

        @Test
        @DisplayName("TC-PA-10: Null DataSource causes NullPointerException")
        void testNullDataSourceCausesError() throws ServletException, IOException {
            // Arrange
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(null);

            // Act & Assert
            assertThrows(NullPointerException.class, () -> {
                productAdminServlet.doGet(request, response);
            });
        }

        @Test
        @DisplayName("TC-PA-11: SQLException during delete - sets error and sends 500")
        void testSqlExceptionDuringDelete() throws Exception {
            // Arrange
            Cart cart = new Cart();
            java.sql.SQLException sqlException = new java.sql.SQLException("Delete error");

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("delete");
            when(request.getParameter("id")).thenReturn("1");
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);
            doThrow(sqlException).when(productDao).doDelete(1);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("error"), 
                eq("Error: sembra esserci un problema con l'elaborazione dei prodotti."));
            verify(response).sendError(eq(500), contains("Delete error"));
        }
    }

    // ============================================================================
    // DOPOST DELEGATION TESTS
    // ============================================================================

    @Nested
    @DisplayName("doPost Delegation Tests")
    class DoPostDelegationTests {

        @Test
        @DisplayName("TC-PA-10: doPost delegates to doGet")
        void testDoPostDelegatesToDoGet() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doPost(request, response);

            // Assert - should behave exactly like doGet
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // PRODUCT LISTING TESTS
    // ============================================================================

    @Nested
    @DisplayName("Product Listing Tests")
    class ProductListingTests {

        @Test
        @DisplayName("TC-PA-11: No sort parameter lists products unsorted")
        void testNoSortParameterListsProductsUnsorted() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert
            verify(request).removeAttribute("products");
            verify(request).setAttribute(eq("products"), any());
        }

        @Test
        @DisplayName("TC-PA-12: Sort by codice parameter")
        void testSortByCodice() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn("codice");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert
            verify(request).getParameter("sort");
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-PA-13: Sort by nome parameter")
        void testSortByNome() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn("nome");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert
            verify(request).getParameter("sort");
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-PA-14: Sort by descrizione parameter")
        void testSortByDescrizione() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn("descrizione");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert
            verify(request).getParameter("sort");
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // REQUEST DISPATCHER TESTS
    // ============================================================================

    @Nested
    @DisplayName("Request Dispatcher Tests")
    class RequestDispatcherTests {

        @Test
        @DisplayName("TC-PA-15: Correct JSP path used for forwarding")
        void testCorrectJspPath() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert
            verify(servletContext).getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp");
        }

        @Test
        @DisplayName("TC-PA-16: Forward is called with request and response")
        void testForwardCalledWithRequestAndResponse() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // CART OPERATIONS TESTS
    // ============================================================================

    @Nested
    @DisplayName("Cart Operations Tests")
    class CartOperationsTests {

        @Test
        @DisplayName("TC-PA-17: Cart is saved to session after operations")
        void testCartSavedToSession() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert
            verify(session).setAttribute("cart", cart);
        }

        @Test
        @DisplayName("TC-PA-18: Multiple products can be added to cart")
        void testMultipleProductsAddedToCart() throws ServletException, IOException {
            // Arrange
            Cart cart = new Cart();
            ProductBean product1 = new ProductBean();
            product1.setCodice(1);
            ProductBean product2 = new ProductBean();
            product2.setCodice(2);
            cart.addProduct(product1);
            cart.addProduct(product2);

            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productAdminServlet.doGet(request, response);

            // Assert
            assertEquals(2, cart.getCartSize());
            verify(session).setAttribute("cart", cart);
        }
    }
}
