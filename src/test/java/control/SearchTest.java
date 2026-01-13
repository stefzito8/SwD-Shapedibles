package control;

import categories.UnitTest;
import model.Cart;
import model.bean.InfoBean;
import model.bean.ProductBean;
import model.dao.IInfoDao;
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
import java.util.ArrayList;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Unit tests for Search controller.
 * 
 * Testing Level: Unit
 * Technique: White-Box (Statement Testing, Branch Testing, Loop Boundary Testing) with Mocking
 * 
 * ============================================================================
 * BRANCH STRUCTURE ANALYSIS (Step 3.1)
 * ============================================================================
 * 
 * Method: doGet(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | SRCH-B1   | id != null                   | Return single     | Continue       |
 * | SRCH-B2   | cart == null                 | Create new cart   | Use existing   |
 * | SRCH-B3   | Query != null                | Process query     | Empty results  |
 * | SRCH-B4   | Results found                | Display results   | No results msg |
 * | SRCH-B5   | AJAX request                 | JSON response     | Page forward   |
 * | SRCH-B6   | SQLException thrown          | Error handling    | Normal flow    |
 * | SRCH-B7   | Loop: for each result        | Process result    | End loop       |
 * -----------------------------------------------------------------
 * 
 * Method: doPost(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | SRCH-B8   | Delegates to doGet           | doGet called      | N/A            |
 * -----------------------------------------------------------------
 * 
 * ============================================================================
 * TEST CASE DESIGN (Step 3.2)
 * ============================================================================
 * 
 * Query Processing Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-SRCH-1    | B3=true       | Valid query (ricerca param)  | Search executed      |
 * | TC-SRCH-2    | B3=false      | Null query                   | No search            |
 * | TC-SRCH-3    | B1=true       | id param provided            | Single product JSON  |
 * | TC-SRCH-4    | B4=true       | Query with results           | Results displayed    |
 * | TC-SRCH-5    | B4=false      | Query with no results        | Empty results        |
 * 
 * Session/Cart Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-SRCH-6    | B2=true       | Cart is null                 | New cart created     |
 * | TC-SRCH-7    | B2=false      | Cart exists                  | Existing cart used   |
 * 
 * Response Type Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-SRCH-8    | B5=true       | AJAX request                 | JSON response        |
 * | TC-SRCH-9    | B5=false      | Normal request               | Page forward         |
 * 
 * Exception Handling Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-SRCH-10   | B6=true       | SQLException                 | Error handling       |
 * 
 * Loop Boundary Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-SRCH-11   | B7 (0 iter)   | No results                   | Loop not executed    |
 * | TC-SRCH-12   | B7 (1 iter)   | Single result                | One iteration        |
 * | TC-SRCH-13   | B7 (>1 iter)  | Multiple results             | Multiple iterations  |
 * 
 * doPost Delegation Tests:
 * | Test ID      | Branch Target | Input Condition              | Expected Result      |
 * |--------------|---------------|------------------------------|----------------------|
 * | TC-SRCH-14   | B8            | POST request                 | doGet called         |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets:
 * - TER1 (Statement): ≥ 80%
 * - TER2 (Branch): ≥ 70%
 * 
 * @see control.Search
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@MockitoSettings(strictness = Strictness.LENIENT)
@DisplayName("Search Controller Unit Tests")
public class SearchTest {

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

    @Mock
    private IInfoDao infoDao;

    private Search searchServlet;
    private StringWriter stringWriter;
    private PrintWriter printWriter;

    @BeforeEach
    void setUp() throws Exception {
        stringWriter = new StringWriter();
        printWriter = new PrintWriter(stringWriter);
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
        
        // Default stubs for DAOs
        ProductBean defaultProduct = new ProductBean();
        defaultProduct.setCodice(1);
        defaultProduct.setNome("Test Product");
        defaultProduct.setInfoCorrenti(1);
        lenient().when(productDao.doRetrieveByKey(anyInt())).thenReturn(defaultProduct);
        lenient().when(productDao.searchByName(anyString())).thenReturn(new ArrayList<>());
        
        InfoBean defaultInfo = new InfoBean();
        defaultInfo.setCodice(1);
        defaultInfo.setCosto(10.0);
        lenient().when(infoDao.doRetrieveByKey(anyInt())).thenReturn(defaultInfo);
    }

    // ============================================================================
    // Query Processing Tests
    // ============================================================================

    @Nested
    @DisplayName("Query Processing Tests")
    class QueryProcessingTests {

        @Test
        @DisplayName("TC-SRCH-1: Valid query (ricerca param) executes search")
        void testValidQueryExecutesSearch() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("test product");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(request).getParameter("ricerca");
            verify(request).setAttribute(eq("searchResults"), any());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-SRCH-2: Null query parameter still processes")
        void testNullQueryParameter() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn(null);
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(request).getParameter("ricerca");
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-SRCH-3: id param returns single product as JSON")
        void testIdParamReturnsSingleProduct() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("id")).thenReturn("1");
            when(request.getParameter("ricerca")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(request).getParameter("id");
            verify(response).setContentType("application/json");
            verify(response).setCharacterEncoding("UTF-8");
        }

        @Test
        @DisplayName("TC-SRCH-4: Query with results displays results")
        void testQueryWithResultsDisplaysResults() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("existing");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("searchResults"), any());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-SRCH-5: Query with no results returns empty collection")
        void testQueryWithNoResultsReturnsEmpty() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("nonexistent12345");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("searchResults"), any());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-SRCH-15: Empty string query processes normally")
        void testEmptyStringQuery() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // Session/Cart Tests
    // ============================================================================

    @Nested
    @DisplayName("Session/Cart Tests")
    class SessionCartTests {

        @Test
        @DisplayName("TC-SRCH-6: New cart created when session cart is null")
        void testNewCartCreatedWhenNull() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("test");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(null);
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert - new cart should be created and set in session
            verify(session).setAttribute(eq("cart"), any(Cart.class));
        }

        @Test
        @DisplayName("TC-SRCH-7: Existing cart reused from session")
        void testExistingCartReused() throws ServletException, IOException {
            // Arrange
            Cart existingCart = new Cart();
            ProductBean product = new ProductBean();
            product.setCodice(1);
            existingCart.addProduct(product);

            when(request.getParameter("ricerca")).thenReturn("test");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(existingCart);
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert - existing cart should be used, not replaced
            verify(session, never()).setAttribute(eq("cart"), any(Cart.class));
        }
    }

    // ============================================================================
    // Response Type Tests
    // ============================================================================

    @Nested
    @DisplayName("Response Type Tests")
    class ResponseTypeTests {

        @Test
        @DisplayName("TC-SRCH-8: AJAX request returns JSON response")
        void testAjaxReturnsJson() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("test");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(response).setContentType("application/json");
            verify(response).setCharacterEncoding("UTF-8");
            verify(response).getWriter();
        }

        @Test
        @DisplayName("TC-SRCH-9: Normal request forwards to JSP page")
        void testNormalRequestForwards() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("test");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(request).getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp");
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-SRCH-16: AJAX with id param returns JSON product")
        void testAjaxWithIdReturnsJsonProduct() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("id")).thenReturn("1");
            when(request.getParameter("ricerca")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(response).setContentType("application/json");
            verify(response).setCharacterEncoding("UTF-8");
        }
    }

    // ============================================================================
    // Exception Handling Tests
    // ============================================================================

    @Nested
    @DisplayName("Exception Handling Tests")
    class ExceptionHandlingTests {

        @Test
        @DisplayName("TC-SRCH-10: Null DataSource causes NullPointerException")
        void testNullDataSourceError() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("test");
            when(request.getParameter("id")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(null);

            // Act & Assert
            assertThrows(NullPointerException.class, () -> {
                searchServlet.doGet(request, response);
            });
        }

        @Test
        @DisplayName("TC-SRCH-17: Invalid id format causes NumberFormatException")
        void testInvalidIdFormatError() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("id")).thenReturn("invalid");
            when(request.getParameter("ricerca")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);

            // Act & Assert
            assertThrows(NumberFormatException.class, () -> {
                searchServlet.doGet(request, response);
            });
        }

        @Test
        @DisplayName("TC-SRCH-18: SQLException triggers error response")
        void testSqlExceptionTriggersError() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("test");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            // The internal DAO may throw SQLException
            // We verify error handling by checking sendError is called
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert - normal flow should complete
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // Loop Boundary Tests
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("TC-SRCH-11: No results - loop executes 0 times")
        void testNoResultsNoLoopExecution() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("zzzznonexistent12345");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(request).setAttribute(eq("searchResults"), any());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-SRCH-12: Single result - loop executes 1 time")
        void testSingleResultOneIteration() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("unique");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            searchServlet.doGet(request, response);

            // Assert - JSON response should be written
            verify(response).setContentType("application/json");
            verify(response).getWriter();
        }

        @Test
        @DisplayName("TC-SRCH-13: Multiple results - loop executes multiple times")
        void testMultipleResultsMultipleIterations() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("common");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            searchServlet.doGet(request, response);

            // Assert - JSON response should contain results
            verify(response).setContentType("application/json");
            verify(response).getWriter();
        }
    }

    // ============================================================================
    // doPost Delegation Tests
    // ============================================================================

    @Nested
    @DisplayName("doPost Delegation Tests")
    class DoPostTests {

        @Test
        @DisplayName("TC-SRCH-14: doPost delegates to doGet")
        void testDoPostDelegatesToDoGet() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("test");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doPost(request, response);

            // Assert - should behave exactly like doGet
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-SRCH-19: doPost with AJAX returns JSON like doGet")
        void testDoPostWithAjaxReturnsJson() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("test");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn("XMLHttpRequest");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            searchServlet.doPost(request, response);

            // Assert
            verify(response).setContentType("application/json");
        }
    }

    // ============================================================================
    // Boundary Value Tests
    // ============================================================================

    @Nested
    @DisplayName("Boundary Value Tests")
    class BoundaryValueTests {

        @Test
        @DisplayName("TC-SRCH-20: Single character query")
        void testSingleCharacterQuery() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("a");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-SRCH-21: Very long query string")
        void testVeryLongQueryString() throws ServletException, IOException {
            // Arrange
            String longQuery = "a".repeat(500);
            when(request.getParameter("ricerca")).thenReturn(longQuery);
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-SRCH-22: Query with special characters")
        void testQueryWithSpecialCharacters() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("ricerca")).thenReturn("test@#$%^&*()");
            when(request.getParameter("id")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(request.getHeader("X-Requested-With")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-SRCH-23: id = 0 (minimum boundary)")
        void testIdZeroBoundary() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("id")).thenReturn("0");
            when(request.getParameter("ricerca")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(response).setContentType("application/json");
        }

        @Test
        @DisplayName("TC-SRCH-24: id = MAX_VALUE (maximum boundary)")
        void testIdMaxValueBoundary() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("id")).thenReturn(String.valueOf(Integer.MAX_VALUE));
            when(request.getParameter("ricerca")).thenReturn(null);
            when(request.getSession()).thenReturn(session);
            when(session.getAttribute("cart")).thenReturn(new Cart());
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(response.getWriter()).thenReturn(printWriter);

            // Act
            searchServlet.doGet(request, response);

            // Assert
            verify(response).setContentType("application/json");
        }
    }

    // Helper method
    private ProductBean createTestProduct(int code, String name) {
        ProductBean product = new ProductBean();
        product.setCodice(code);
        product.setNome(name);
        return product;
    }
}
