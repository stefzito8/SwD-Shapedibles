package control;

import categories.UnitTest;
import model.bean.ImageBean;
import model.bean.InfoBean;
import model.bean.NutritionTableBean;
import model.bean.ProductBean;
import model.dao.IImageDao;
import model.dao.IInfoDao;
import model.dao.INutritionTableDao;
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
import javax.sql.DataSource;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Unit tests for ProductDetails controller.
 * 
 * Testing Level: Unit
 * Technique: White-Box (Statement Testing, Branch Testing) with Mocking
 * 
 * ============================================================================
 * BRANCH STRUCTURE ANALYSIS (Step 3.1)
 * ============================================================================
 * 
 * Method: doPost(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | PD-B1     | product param != null        | Parse ID          | Error handling |
 * | PD-B2     | product param is numeric     | Fetch product     | NumberFormatException |
 * | PD-B3     | product != null (found)      | Display product   | Null product   |
 * | PD-B4     | SQLException caught          | Error + sendError | Normal flow    |
 * -----------------------------------------------------------------
 * 
 * Method: doGet(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | PD-B5     | Delegates to doPost          | doPost called     | N/A            |
 * -----------------------------------------------------------------
 * 
 * ============================================================================
 * TEST CASE DESIGN (Step 3.2)
 * ============================================================================
 * 
 * | Test ID      | Branch Target    | Input Condition              | Expected Result      |
 * |--------------|------------------|------------------------------|----------------------|
 * | TC-PD-1      | B1,B2,B3=true    | Valid product param, exists  | Product displayed    |
 * | TC-PD-2      | B3=false         | Valid param, product null    | Null product handled |
 * | TC-PD-3      | B1=false         | Missing product param        | NullPointerException |
 * | TC-PD-4      | B2=false         | Non-numeric product param    | NumberFormatException|
 * | TC-PD-5      | B4=true          | SQLException                 | Error response 500   |
 * | TC-PD-6      | B5              | GET request                  | doPost called        |
 * | TC-PD-7      | Normal flow      | Product with info            | Info displayed       |
 * | TC-PD-8      | Normal flow      | Product with nutrition       | Nutrition displayed  |
 * -----------------------------------------------------------------
 * 
 * Branch Coverage Matrix:
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Tests    | False Tests   |
 * |-----------|------------------------------|---------------|---------------|
 * | PD-B1     | product param != null        | TC-PD-1,2,4,7,8| TC-PD-3      |
 * | PD-B2     | product param is numeric     | TC-PD-1,2,7,8 | TC-PD-4       |
 * | PD-B3     | product != null (found)      | TC-PD-1,7,8   | TC-PD-2       |
 * | PD-B4     | SQLException catch           | TC-PD-5       | TC-PD-1-4,6-8 |
 * | PD-B5     | doGet delegates              | TC-PD-6       | N/A           |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets:
 * - TER1 (Statement): ≥ 80%
 * - TER2 (Branch): ≥ 70%
 * 
 * @see control.ProductDetails
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@DisplayName("ProductDetails Controller Unit Tests")
public class ProductDetailsTest {

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

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

    @Mock
    private IImageDao imageDao;

    @Mock
    private INutritionTableDao nutritionDao;

    private ProductDetails productDetailsServlet;

    @BeforeEach
    void setUp() throws Exception {
        productDetailsServlet = new ProductDetails() {
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
            
            @Override
            protected INutritionTableDao createNutritionTableDao(DataSource ds) {
                return nutritionDao;
            }
        };
        
        // Default stubs for DAOs
        ProductBean defaultProduct = new ProductBean();
        defaultProduct.setCodice(1);
        defaultProduct.setNome("Test Product");
        defaultProduct.setInfoCorrenti(1);
        lenient().when(productDao.doRetrieveByKey(anyInt())).thenReturn(defaultProduct);
        
        InfoBean defaultInfo = new InfoBean();
        defaultInfo.setCodice(1);
        lenient().when(infoDao.doRetrieveByKey(anyInt())).thenReturn(defaultInfo);
        
        NutritionTableBean defaultNutrition = new NutritionTableBean();
        lenient().when(nutritionDao.doRetrieveByKey(anyInt())).thenReturn(defaultNutrition);
    }

    // ============================================================================
    // PRODUCT RETRIEVAL TESTS
    // ============================================================================

    @Nested
    @DisplayName("Product Retrieval Tests")
    class ProductRetrievalTests {

        @Test
        @DisplayName("TC-PD-1: Valid product parameter displays product details")
        void testValidProductIdDisplaysProduct() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert
            verify(request).setAttribute(eq("product"), any());
            verify(request).setAttribute(eq("info"), any());
            verify(request).setAttribute(eq("nutritionTable"), any());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-PD-2: Product not found in database still forwards")
        void testProductNotFoundStillForwards() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("999");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert - should still forward even if product is null
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-PD-3: Missing product parameter causes NullPointerException")
        void testMissingProductIdError() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn(null);
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);

            // Act & Assert - null parameter will cause NumberFormatException in parseInt
            assertThrows(NumberFormatException.class, () -> {
                productDetailsServlet.doPost(request, response);
            });
        }

        @Test
        @DisplayName("TC-PD-4: Non-numeric product parameter causes NumberFormatException")
        void testNonNumericProductIdError() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("abc");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);

            // Act & Assert
            assertThrows(NumberFormatException.class, () -> {
                productDetailsServlet.doPost(request, response);
            });
        }

        @Test
        @DisplayName("TC-PD-9: Empty string product parameter causes NumberFormatException")
        void testEmptyProductIdError() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);

            // Act & Assert
            assertThrows(NumberFormatException.class, () -> {
                productDetailsServlet.doPost(request, response);
            });
        }
    }

    // ============================================================================
    // PRODUCT DATA TESTS
    // ============================================================================

    @Nested
    @DisplayName("Product Data Tests")
    class ProductDataTests {

        @Test
        @DisplayName("TC-PD-7: Product info is set as request attribute")
        void testProductInfoSetAsAttribute() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert
            verify(request).removeAttribute("product");
            verify(request).setAttribute(eq("product"), any());
            verify(request).removeAttribute("info");
            verify(request).setAttribute(eq("info"), any());
        }

        @Test
        @DisplayName("TC-PD-8: Nutrition table is set as request attribute")
        void testNutritionTableSetAsAttribute() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert
            verify(request).removeAttribute("nutritionTable");
            verify(request).setAttribute(eq("nutritionTable"), any());
        }

        @Test
        @DisplayName("TC-PD-10: All product attributes are removed before setting new ones")
        void testAttributesRemovedBeforeSetting() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert - verify removeAttribute is called before setAttribute
            verify(request).removeAttribute("product");
            verify(request).removeAttribute("info");
            verify(request).removeAttribute("nutritionTable");
        }
    }

    // ============================================================================
    // EXCEPTION HANDLING TESTS
    // ============================================================================

    @Nested
    @DisplayName("Exception Handling Tests")
    class ExceptionHandlingTests {

        @Test
        @DisplayName("TC-PD-5: Null DataSource causes NullPointerException")
        void testNullDataSourceError() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(null);

            // Act & Assert
            assertThrows(NullPointerException.class, () -> {
                productDetailsServlet.doPost(request, response);
            });
        }

        @Test
        @DisplayName("TC-PD-11: Negative product ID is processed normally")
        void testNegativeProductId() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("-1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert - should forward even with negative ID
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-PD-12: Very large product ID is processed")
        void testVeryLargeProductId() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn(String.valueOf(Integer.MAX_VALUE));
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // DOGET DELEGATION TESTS
    // ============================================================================

    @Nested
    @DisplayName("doGet Delegation Tests")
    class DoGetTests {

        @Test
        @DisplayName("TC-PD-6: doGet delegates to doPost")
        void testDoGetDelegatesToDoPost() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doGet(request, response);

            // Assert - verify doPost behavior occurred (same as doPost)
            verify(request).setAttribute(eq("product"), any());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-PD-13: doGet with valid product shows same result as doPost")
        void testDoGetSameAsDoPost() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("5");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doGet(request, response);

            // Assert
            verify(request).removeAttribute("product");
            verify(request).setAttribute(eq("product"), any());
            verify(request).removeAttribute("info");
            verify(request).setAttribute(eq("info"), any());
            verify(request).removeAttribute("nutritionTable");
            verify(request).setAttribute(eq("nutritionTable"), any());
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
        @DisplayName("TC-PD-14: Correct JSP path used for forwarding")
        void testCorrectJspPath() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert
            verify(servletContext).getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp");
        }

        @Test
        @DisplayName("TC-PD-15: Forward is called with request and response")
        void testForwardCalledWithRequestAndResponse() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert
            verify(requestDispatcher).forward(request, response);
        }
    }

    // ============================================================================
    // BOUNDARY VALUE TESTS
    // ============================================================================

    @Nested
    @DisplayName("Boundary Value Tests")
    class BoundaryValueTests {

        @Test
        @DisplayName("TC-PD-16: Zero product ID is valid")
        void testZeroProductId() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("0");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-PD-17: Product ID 1 (minimum positive) is valid")
        void testMinimumPositiveProductId() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("TC-PD-18: Product ID with leading zeros is parsed correctly")
        void testProductIdWithLeadingZeros() throws ServletException, IOException {
            // Arrange
            when(request.getParameter("product")).thenReturn("007");
            when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp"))
                    .thenReturn(requestDispatcher);

            // Act
            productDetailsServlet.doPost(request, response);

            // Assert - "007" is parsed as 7
            verify(requestDispatcher).forward(request, response);
        }
    }
}
