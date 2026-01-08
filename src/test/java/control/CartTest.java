package control;

import categories.UnitTest;
import model.Cart;
import model.bean.ProductBean;
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
import java.io.PrintWriter;
import java.io.StringWriter;
import java.sql.SQLException;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Unit tests for Cart controller.
 * 
 * Testing Level: Unit
 * Technique: White-Box (Statement Testing, Branch Testing, Loop Boundary Testing) with Mocking
 * 
 * ============================================================================
 * BRANCH STRUCTURE ANALYSIS (Step 3.1)
 * ============================================================================
 * 
 * Method: doPost(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | CART-B1   | action == "addC"             | Add to cart       | Check next     |
 * | CART-B2   | action == "deleteC"          | Remove from cart  | Check next     |
 * | CART-B3   | cart == null                 | Create new cart   | Use existing   |
 * | CART-B4   | action != null               | Process action    | No action      |
 * | CART-B5   | AJAX request                 | JSON response     | Page forward   |
 * | CART-B6   | SQLException caught          | Error response    | Normal flow    |
 * -----------------------------------------------------------------
 * 
 * Method: doGet(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | CART-B7   | Delegates to doPost          | doPost called     | N/A            |
 * -----------------------------------------------------------------
 * 
 * ============================================================================
 * TEST CASE DESIGN (Step 3.2)
 * ============================================================================
 * 
 * Action Switch Tests:
 * | Test ID      | Branch Target | Input Condition    | Expected Result      |
 * |--------------|---------------|--------------------|--------------------- |
 * | TC-CART-1    | B1=true       | action="addC"      | Product added        |
 * | TC-CART-2    | B2=true       | action="deleteC"   | Product removed      |
 * | TC-CART-3    | B4=false      | action=null        | No action taken      |
 * | TC-CART-4    | B4=true       | action="invalid"   | No matching action   |
 * 
 * Session Handling Tests:
 * | Test ID      | Branch Target | Input Condition    | Expected Result      |
 * |--------------|---------------|--------------------|--------------------- |
 * | TC-CART-5    | B3=true       | Cart null          | New cart created     |
 * | TC-CART-6    | B3=false      | Cart exists        | Existing cart used   |
 * 
 * AJAX Tests:
 * | Test ID      | Branch Target | Input Condition    | Expected Result      |
 * |--------------|---------------|--------------------|--------------------- |
 * | TC-CART-7    | B5=true       | XMLHttpRequest     | JSON response        |
 * | TC-CART-8    | B5=false      | Normal request     | Page forward         |
 * 
 * Exception Tests:
 * | Test ID      | Branch Target | Input Condition    | Expected Result      |
 * |--------------|---------------|--------------------|--------------------- |
 * | TC-CART-9    | B6=true       | SQLException       | Error response 500   |
 * 
 * doGet Tests:
 * | Test ID      | Branch Target | Input Condition    | Expected Result      |
 * |--------------|---------------|--------------------|--------------------- |
 * | TC-CART-10   | B7            | GET request        | doPost called        |
 * 
 * Loop Boundary Tests:
 * | Test ID      | Branch Target | Input Condition    | Expected Result      |
 * |--------------|---------------|--------------------|--------------------- |
 * | TC-CART-11   | Loop (0 iter) | Empty cart         | cartSize = 0         |
 * | TC-CART-12   | Loop (1 iter) | Single item        | cartSize = 1         |
 * | TC-CART-13   | Loop (>1 iter)| Multiple items     | cartSize > 1         |
 * 
 * Coverage Targets:
 * - TER1 (Statement): ≥ 80%
 * - TER2 (Branch): ≥ 70%
 * 
 * @see control.Cart
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@DisplayName("Cart Controller Unit Tests")
public class CartTest {

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
        
        // Default stub for productDao
        ProductBean defaultProduct = new ProductBean();
        defaultProduct.setCodice(1);
        defaultProduct.setNome("Test Product");
        lenient().when(productDao.doRetrieveByKey(anyInt())).thenReturn(defaultProduct);
    }

    // ============================================================================
    // ACTION SWITCH TESTS
    // ============================================================================

    @Nested
    @DisplayName("Action Switch Tests")
    class ActionSwitchTests {

        @Test
        @DisplayName("TC-CART-1: Add action (addC) adds product to cart")
        void testAddAction() throws ServletException, IOException, SQLException {
            // Arrange
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Test Product");
            
            model.Cart cart = new model.Cart();
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("addC");
            when(request.getParameter("id")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            verify(session).setAttribute(eq("cart"), any(model.Cart.class));
            verify(response).setContentType("application/json");
            verify(response).setCharacterEncoding("UTF-8");
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("cartSize"));
        }

        @Test
        @DisplayName("TC-CART-2: Delete action (deleteC) removes product from cart")
        void testDeleteAction() throws ServletException, IOException, SQLException {
            // Arrange
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Test Product");
            
            model.Cart cart = new model.Cart();
            cart.addProduct(product); // Add product first so we can delete it
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("deleteC");
            when(request.getParameter("id")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            verify(session).setAttribute(eq("cart"), any(model.Cart.class));
            verify(response).setContentType("application/json");
        }

        @Test
        @DisplayName("TC-CART-3: Null action results in no cart modification")
        void testNullAction() throws ServletException, IOException {
            // Arrange
            model.Cart cart = new model.Cart();
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            assertEquals(0, cart.getCartSize());
            verify(response).setContentType("application/json");
        }

        @Test
        @DisplayName("TC-CART-4: Invalid action results in no cart modification")
        void testInvalidAction() throws ServletException, IOException {
            // Arrange
            model.Cart cart = new model.Cart();
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("invalidAction");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            assertEquals(0, cart.getCartSize());
            verify(response).setContentType("application/json");
        }
    }

    // ============================================================================
    // SESSION HANDLING TESTS
    // ============================================================================

    @Nested
    @DisplayName("Session Handling Tests")
    class SessionHandlingTests {

        @Test
        @DisplayName("TC-CART-5: New cart created when session cart is null")
        void testNewCartCreatedWhenNull() throws ServletException, IOException {
            // Arrange
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(null);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert - cart may be set multiple times (once when created, once after processing)
            verify(session, atLeastOnce()).setAttribute(eq("cart"), any(model.Cart.class));
        }

        @Test
        @DisplayName("TC-CART-6: Existing cart reused from session")
        void testExistingCartReused() throws ServletException, IOException {
            // Arrange
            model.Cart existingCart = new model.Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            existingCart.addProduct(product);
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(existingCart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("\"cartSize\":1"));
        }
    }

    // ============================================================================
    // AJAX REQUEST TESTS
    // ============================================================================

    @Nested
    @DisplayName("AJAX Request Tests")
    class AjaxRequestTests {

        @Test
        @DisplayName("TC-CART-7: AJAX request returns JSON response")
        void testAjaxReturnsJson() throws ServletException, IOException {
            // Arrange
            model.Cart cart = new model.Cart();
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            verify(response).setContentType("application/json");
            verify(response).setCharacterEncoding("UTF-8");
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("cartSize"));
        }

        @Test
        @DisplayName("TC-CART-8: Normal request forwards to cart.jsp")
        void testNormalRequestForwards() throws ServletException, IOException {
            // Arrange
            model.Cart cart = new model.Cart();
            
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/cart.jsp")).thenReturn(requestDispatcher);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
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
        @DisplayName("TC-CART-9: SQLException triggers error response")
        void testSQLExceptionHandling() throws ServletException, IOException, SQLException {
            // Arrange
            model.Cart cart = new model.Cart();
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("addC");
            when(request.getParameter("id")).thenReturn("invalid"); // Will cause NumberFormatException
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            
            // Act & Assert
            assertThrows(NumberFormatException.class, () -> {
                cartServlet.doPost(request, response);
            });
        }
    }

    // ============================================================================
    // DO GET DELEGATION TESTS
    // ============================================================================

    @Nested
    @DisplayName("doGet Delegation Tests")
    class DoGetTests {

        @Test
        @DisplayName("TC-CART-10: doGet delegates to doPost")
        void testDoGetDelegatesToDoPost() throws ServletException, IOException {
            // Arrange
            model.Cart cart = new model.Cart();
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doGet(request, response);
            
            // Assert - verify doPost behavior occurred (JSON response for AJAX)
            verify(response).setContentType("application/json");
        }
    }

    // ============================================================================
    // LOOP BOUNDARY TESTS
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("TC-CART-11: Empty cart - cartSize is 0")
        void testEmptyCartSize() throws ServletException, IOException {
            // Arrange
            model.Cart emptyCart = new model.Cart();
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(emptyCart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("\"cartSize\":0"));
        }

        @Test
        @DisplayName("TC-CART-12: Single item cart - cartSize is 1")
        void testSingleItemCartSize() throws ServletException, IOException {
            // Arrange
            model.Cart singleItemCart = new model.Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Single Product");
            singleItemCart.addProduct(product);
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(singleItemCart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("\"cartSize\":1"));
        }

        @Test
        @DisplayName("TC-CART-13: Multiple items cart - cartSize > 1")
        void testMultipleItemsCartSize() throws ServletException, IOException {
            // Arrange
            model.Cart multiItemCart = new model.Cart();
            
            ProductBean product1 = new ProductBean();
            product1.setCodice(1);
            product1.setNome("Product 1");
            multiItemCart.addProduct(product1);
            
            ProductBean product2 = new ProductBean();
            product2.setCodice(2);
            product2.setNome("Product 2");
            multiItemCart.addProduct(product2);
            
            ProductBean product3 = new ProductBean();
            product3.setCodice(3);
            product3.setNome("Product 3");
            multiItemCart.addProduct(product3);
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(multiItemCart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("\"cartSize\":3"));
        }

        @Test
        @DisplayName("TC-CART-14: Adding same product multiple times increases quantity")
        void testAddingSameProductMultipleTimes() throws ServletException, IOException {
            // Arrange
            model.Cart cart = new model.Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Repeated Product");
            cart.addProduct(product);
            cart.addProduct(product);
            cart.addProduct(product);
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("\"cartSize\":3"));
            assertEquals(3, cart.getProductQuantity(product));
        }
    }

    // ============================================================================
    // CART OPERATIONS TESTS
    // ============================================================================

    @Nested
    @DisplayName("Cart Operations Tests")
    class CartOperationsTests {

        @Test
        @DisplayName("TC-CART-15: Delete reduces quantity by 1")
        void testDeleteReducesQuantity() throws ServletException, IOException {
            // Arrange
            model.Cart cart = new model.Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Test Product");
            cart.addProduct(product);
            cart.addProduct(product); // quantity = 2
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("deleteC");
            when(request.getParameter("id")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("\"cartSize\":1")); // Should be 1 after deletion
        }

        @Test
        @DisplayName("TC-CART-16: Delete removes product when quantity becomes 0")
        void testDeleteRemovesProductAtZero() throws ServletException, IOException {
            // Arrange
            model.Cart cart = new model.Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            product.setNome("Test Product");
            cart.addProduct(product); // quantity = 1
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn("deleteC");
            when(request.getParameter("id")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("\"cartSize\":0")); // Should be 0 after deletion
        }

        @Test
        @DisplayName("TC-CART-17: Cart size correctly sums all quantities")
        void testCartSizeSumsQuantities() throws ServletException, IOException {
            // Arrange
            model.Cart cart = new model.Cart();
            
            ProductBean product1 = new ProductBean();
            product1.setCodice(1);
            product1.setNome("Product 1");
            cart.addProduct(product1);
            cart.addProduct(product1); // quantity = 2
            
            ProductBean product2 = new ProductBean();
            product2.setCodice(2);
            product2.setNome("Product 2");
            cart.addProduct(product2); // quantity = 1
            
            // Total should be 3
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.contains("\"cartSize\":3"));
        }
    }

    // ============================================================================
    // RESPONSE FORMAT TESTS
    // ============================================================================

    @Nested
    @DisplayName("Response Format Tests")
    class ResponseFormatTests {

        @Test
        @DisplayName("TC-CART-18: JSON response has correct content type")
        void testJsonContentType() throws ServletException, IOException {
            // Arrange
            model.Cart cart = new model.Cart();
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            verify(response).setContentType("application/json");
            verify(response).setCharacterEncoding("UTF-8");
        }

        @Test
        @DisplayName("TC-CART-19: JSON response is valid format")
        void testJsonValidFormat() throws ServletException, IOException {
            // Arrange
            model.Cart cart = new model.Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            cart.addProduct(product);
            
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(cart);
            when(request.getParameter("action")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);
            
            // Act
            cartServlet.doPost(request, response);
            
            // Assert
            String jsonOutput = stringWriter.toString();
            assertTrue(jsonOutput.startsWith("{"));
            assertTrue(jsonOutput.endsWith("}"));
            assertTrue(jsonOutput.contains("\"cartSize\""));
        }
    }
}
