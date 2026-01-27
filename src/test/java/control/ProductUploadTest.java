package control;

import categories.UnitTest;
import model.bean.ImageBean;
import model.bean.InfoBean;
import model.bean.ProductBean;
import model.datasource.ImageDaoDataSource;
import model.datasource.InfoDaoDataSource;
import model.datasource.ProductDaoDataSource;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.MockedConstruction;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletContext;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import javax.servlet.http.Part;
import javax.sql.DataSource;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Unit tests for ProductUpload controller.
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
 * | Branch ID | Condition                    | True Path           | False Path       |
 * |-----------|------------------------------|---------------------|------------------|
 * | PU-B1     | request.getParts() != null   | Process file parts  | Skip file upload |
 * | PU-B2     | getParts().size() > 0        | Iterate parts       | Skip iteration   |
 * | PU-B3     | fileName != null || != ""    | Validate file       | Set error        |
 * | PU-B4     | isValidFileType()            | Check size          | Set error        |
 * | PU-B5     | fileSize <= 5MB              | Check magic number  | Set error        |
 * | PU-B6     | isValidMagicNumber()         | Write file          | Set error        |
 * | PU-B7     | SQLException caught          | Print error         | Normal flow      |
 * -----------------------------------------------------------------
 * 
 * Method: doGet(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path           | False Path       |
 * |-----------|------------------------------|---------------------|------------------|
 * | PU-B8     | Delegates to doPost          | doPost called       | N/A              |
 * -----------------------------------------------------------------
 * 
 * Private Helper Methods:
 * -----------------------------------------------------------------
 * | Method              | Branches                                              |
 * |---------------------|-------------------------------------------------------|
 * | extractFileName()   | Loop over content-disposition items, filename check  |
 * | getFileExtension()  | fileName != null && contains "."                     |
 * | isValidFileType()   | Loop over allowed types (jpg, jpeg, png, gif, bmp)   |
 * | isValidMagicNumber()| Check JPG/PNG/GIF/BMP magic bytes                    |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@DisplayName("ProductUpload Controller Tests")
public class ProductUploadTest {
    
    @Mock
    private HttpServletRequest request;
    
    @Mock
    private HttpServletResponse response;
    
    @Mock
    private ServletContext servletContext;
    
    @Mock
    private RequestDispatcher dispatcher;
    
    @Mock
    private DataSource dataSource;
    
    @Mock
    private HttpSession session;
    
    @Mock
    private Part mockPart;
    
    private ProductUpload servlet;
    
    @BeforeEach
    void setUp() throws Exception {
        servlet = new ProductUpload() {
            @Override
            public ServletContext getServletContext() {
                return servletContext;
            }
        };
        
        // Common mock setup
        when(request.getServletContext()).thenReturn(servletContext);
        when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
        when(servletContext.getRealPath("")).thenReturn("C:\\test\\webapp\\");
        when(request.getSession()).thenReturn(session);
    }
    
    // ========================================================================
    // doGet Tests
    // ========================================================================
    
    @Nested
    @DisplayName("doGet Tests")
    class DoGetTests {
        
        @Test
        @DisplayName("doGet delegates to doPost")
        void testDoGetDelegatesToDoPost() throws ServletException, IOException, SQLException {
            // Setup minimal valid parameters
            when(request.getParameter("name")).thenReturn("Test Product");
            when(request.getParameter("description")).thenReturn("Test Description");
            when(request.getParameter("price")).thenReturn("10.00");
            when(request.getParameter("quantity")).thenReturn("100");
            when(request.getParameter("type")).thenReturn("Category");
            when(request.getParts()).thenReturn(Collections.emptyList());
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doGet(request, response);
                
                // Verify forward to admin page
                verify(dispatcher).forward(request, response);
            }
        }
    }
    
    // ========================================================================
    // Product Creation Tests
    // ========================================================================
    
    @Nested
    @DisplayName("Product Creation Tests")
    class ProductCreationTests {
        
        @BeforeEach
        void setUpProductParams() {
            when(request.getParameter("name")).thenReturn("New Product");
            when(request.getParameter("description")).thenReturn("Product description");
            when(request.getParameter("price")).thenReturn("25.99");
            when(request.getParameter("quantity")).thenReturn("50");
            when(request.getParameter("type")).thenReturn("Sweets");
        }
        
        @Test
        @DisplayName("Successfully creates product with all required fields")
        void testSuccessfulProductCreation() throws ServletException, IOException, SQLException {
            when(request.getParts()).thenReturn(Collections.emptyList());
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName("New Product")).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName("New Product")).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Verify info was saved
                assertFalse(infoDaoMock.constructed().isEmpty());
                verify(infoDaoMock.constructed().get(0)).doSave(any(InfoBean.class));
                
                // Verify product was saved with correct properties (kills setter mutations lines 119-120)
                assertFalse(prodDaoMock.constructed().isEmpty());
                verify(prodDaoMock.constructed().get(0)).doSave(argThat(prod -> 
                    prod.getInfoCorrenti() == 1 &&
                    "New Product".equals(prod.getNome())
                ));
                
                // Verify forward to admin page
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Product creation saves info bean with correct values")
        void testInfoBeanSavedCorrectly() throws ServletException, IOException, SQLException {
            when(request.getParts()).thenReturn(Collections.emptyList());
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName("New Product")).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Verify doSave was called on InfoDaoDataSource
                verify(infoDaoMock.constructed().get(0)).doSave(argThat(info -> 
                    "New Product".equals(info.getNome()) &&
                    "Product description".equals(info.getDescrizione()) &&
                    25.99 == info.getCosto() &&
                    50 == info.getDisponibilità() &&
                    "Sweets".equals(info.getTipologia())
                ));
            }
        }
    }
    
    // ========================================================================
    // File Upload Tests
    // ========================================================================
    
    @Nested
    @DisplayName("File Upload Tests")
    class FileUploadTests {
        
        @BeforeEach
        void setUpFileUpload() {
            when(request.getParameter("name")).thenReturn("Product");
            when(request.getParameter("description")).thenReturn("Description");
            when(request.getParameter("price")).thenReturn("10.00");
            when(request.getParameter("quantity")).thenReturn("10");
            when(request.getParameter("type")).thenReturn("Type");
        }
        
        @Test
        @DisplayName("Valid JPG file is uploaded successfully")
        void testValidJpgUpload() throws ServletException, IOException, SQLException {
            // Setup valid JPG file
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"product.jpg\"");
            when(mockPart.getSize()).thenReturn(1000L);
            byte[] jpgMagic = new byte[]{(byte)0xFF, (byte)0xD8, (byte)0xFF, (byte)0xE0};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(jpgMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Verify file was written
                verify(mockPart).write(contains("product.jpg"));
                
                // Verify image was saved to database with correct properties (kills setter mutations lines 124-125)
                assertFalse(imgDaoMock.constructed().isEmpty());
                verify(imgDaoMock.constructed().get(0)).doSave(argThat(img -> 
                    img.getCodiceProdotto() == 1 &&
                    img.getImg() != null
                ));
            }
        }
        
        @Test
        @DisplayName("Valid PNG file is uploaded successfully")
        void testValidPngUpload() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"product.png\"");
            when(mockPart.getSize()).thenReturn(1000L);
            byte[] pngMagic = new byte[]{(byte)0x89, 'P', 'N', 'G'};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(pngMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(mockPart).write(contains("product.png"));
            }
        }
        
        @Test
        @DisplayName("Valid GIF file is uploaded successfully")
        void testValidGifUpload() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"product.gif\"");
            when(mockPart.getSize()).thenReturn(1000L);
            byte[] gifMagic = new byte[]{'G', 'I', 'F', '8'};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(gifMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(mockPart).write(contains("product.gif"));
            }
        }
        
        @Test
        @DisplayName("Valid BMP file is uploaded successfully")
        void testValidBmpUpload() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"product.bmp\"");
            when(mockPart.getSize()).thenReturn(1000L);
            byte[] bmpMagic = new byte[]{'B', 'M', 0x00, 0x00};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(bmpMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(mockPart).write(contains("product.bmp"));
            }
        }
        
        @Test
        @DisplayName("Invalid file extension sets error")
        void testInvalidFileExtension() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"virus.exe\"");
            lenient().when(mockPart.getSize()).thenReturn(1000L);
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Error should be set (note: in source, error message is same for all errors)
                verify(request).setAttribute(eq("error"), anyString());
                verify(mockPart, never()).write(anyString());
            }
        }
        
        @Test
        @DisplayName("File too large sets error")
        void testFileTooLarge() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"large.jpg\"");
            when(mockPart.getSize()).thenReturn(10 * 1024 * 1024L); // 10MB
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute(eq("error"), anyString());
                verify(mockPart, never()).write(anyString());
            }
        }
        
        @Test
        @DisplayName("Invalid magic number sets error")
        void testInvalidMagicNumber() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"fake.jpg\"");
            when(mockPart.getSize()).thenReturn(1000L);
            // Invalid magic number
            byte[] invalidMagic = new byte[]{0x00, 0x00, 0x00, 0x00};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(invalidMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute(eq("error"), anyString());
                verify(mockPart, never()).write(anyString());
            }
        }
    }
    
    // ========================================================================
    // Exception Handling Tests
    // ========================================================================
    
    @Nested
    @DisplayName("Exception Handling Tests")
    class ExceptionHandlingTests {
        
        @BeforeEach
        void setUpParams() {
            lenient().when(request.getParameter("name")).thenReturn("Product");
            lenient().when(request.getParameter("description")).thenReturn("Description");
            lenient().when(request.getParameter("price")).thenReturn("10.00");
            lenient().when(request.getParameter("quantity")).thenReturn("10");
            lenient().when(request.getParameter("type")).thenReturn("Type");
        }
        
        @Test
        @DisplayName("SQLException during save is caught")
        void testSqlExceptionHandled() throws ServletException, IOException, SQLException {
            when(request.getParts()).thenReturn(Collections.emptyList());
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        doThrow(new SQLException("Database error")).when(mock).doSave(any(InfoBean.class));
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class);
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                // Should not throw - exception is caught internally
                assertDoesNotThrow(() -> servlet.doPost(request, response));
                
                // Forward should still happen
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("NumberFormatException for invalid price")
        void testInvalidPriceFormat() throws ServletException, IOException, SQLException {
            when(request.getParameter("price")).thenReturn("not-a-number");
            when(request.getParts()).thenReturn(Collections.emptyList());
            
            assertThrows(NumberFormatException.class, () -> servlet.doPost(request, response));
        }
        
        @Test
        @DisplayName("NumberFormatException for invalid quantity")
        void testInvalidQuantityFormat() throws ServletException, IOException, SQLException {
            when(request.getParameter("quantity")).thenReturn("abc");
            when(request.getParts()).thenReturn(Collections.emptyList());
            
            assertThrows(NumberFormatException.class, () -> servlet.doPost(request, response));
        }
    }
    
    // ========================================================================
    // Boundary Value Tests
    // ========================================================================
    
    @Nested
    @DisplayName("Boundary Value Tests")
    class BoundaryValueTests {
        
        @BeforeEach
        void setUpParams() {
            when(request.getParameter("name")).thenReturn("Product");
            when(request.getParameter("description")).thenReturn("Description");
            when(request.getParameter("price")).thenReturn("10.00");
            when(request.getParameter("quantity")).thenReturn("10");
            when(request.getParameter("type")).thenReturn("Type");
        }
        
        @Test
        @DisplayName("File exactly at 5MB limit is accepted")
        void testFileAtExactLimit() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.jpg\"");
            when(mockPart.getSize()).thenReturn(5L * 1024 * 1024); // Exactly 5MB
            byte[] jpgMagic = new byte[]{(byte)0xFF, (byte)0xD8, (byte)0xFF, (byte)0xE0};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(jpgMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // File should be accepted
                verify(mockPart).write(anyString());
            }
        }
        
        @Test
        @DisplayName("File 1 byte over 5MB limit is rejected")
        void testFileOneByteOverLimit() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.jpg\"");
            when(mockPart.getSize()).thenReturn(5L * 1024 * 1024 + 1); // 5MB + 1 byte
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // File should be rejected
                verify(request).setAttribute(eq("error"), anyString());
                verify(mockPart, never()).write(anyString());
            }
        }
        
        @Test
        @DisplayName("Zero price is accepted")
        void testZeroPrice() throws ServletException, IOException, SQLException {
            when(request.getParameter("price")).thenReturn("0.00");
            when(request.getParts()).thenReturn(Collections.emptyList());
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                assertDoesNotThrow(() -> servlet.doPost(request, response));
            }
        }
        
        @Test
        @DisplayName("Zero quantity is accepted")
        void testZeroQuantity() throws ServletException, IOException, SQLException {
            when(request.getParameter("quantity")).thenReturn("0");
            when(request.getParts()).thenReturn(Collections.emptyList());
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                assertDoesNotThrow(() -> servlet.doPost(request, response));
            }
        }
    }
    
    // ========================================================================
    // Loop Boundary Tests
    // ========================================================================
    
    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {
        
        @BeforeEach
        void setUpParams() {
            when(request.getParameter("name")).thenReturn("Product");
            when(request.getParameter("description")).thenReturn("Description");
            when(request.getParameter("price")).thenReturn("10.00");
            when(request.getParameter("quantity")).thenReturn("10");
            when(request.getParameter("type")).thenReturn("Type");
        }
        
        @Test
        @DisplayName("Zero file parts - no file processing")
        void testZeroFileParts() throws ServletException, IOException, SQLException {
            when(request.getParts()).thenReturn(Collections.emptyList());
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Product should still be created
                verify(prodDaoMock.constructed().get(0)).doSave(any(ProductBean.class));
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Null file parts collection handled")
        void testNullFileParts() throws ServletException, IOException, SQLException {
            when(request.getParts()).thenReturn(null);
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                // Should handle null gracefully
                assertDoesNotThrow(() -> servlet.doPost(request, response));
            }
        }
        
        @Test
        @DisplayName("Single file part processed")
        void testSingleFilePart() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.jpg\"");
            when(mockPart.getSize()).thenReturn(1000L);
            byte[] jpgMagic = new byte[]{(byte)0xFF, (byte)0xD8, (byte)0xFF, (byte)0xE0};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(jpgMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(mockPart).write(anyString());
            }
        }
    }
    
    // ========================================================================
    // Helper Method Tests (via behavior)
    // ========================================================================
    
    @Nested
    @DisplayName("Helper Method Behavior Tests")
    class HelperMethodTests {
        
        @BeforeEach
        void setUpParams() {
            when(request.getParameter("name")).thenReturn("Product");
            when(request.getParameter("description")).thenReturn("Description");
            when(request.getParameter("price")).thenReturn("10.00");
            when(request.getParameter("quantity")).thenReturn("10");
            when(request.getParameter("type")).thenReturn("Type");
        }
        
        @Test
        @DisplayName("extractFileName handles no filename in content-disposition")
        void testExtractFileNameNoFilename() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\""); // No filename
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Should complete without writing file
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("getFileExtension handles filename with no extension")
        void testNoFileExtension() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"noextension\"");
            lenient().when(mockPart.getSize()).thenReturn(1000L);
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Should set error for invalid file type
                verify(request).setAttribute(eq("error"), anyString());
            }
        }
        
        @Test
        @DisplayName("isValidFileType accepts JPEG extension")
        void testJpegExtension() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.jpeg\"");
            when(mockPart.getSize()).thenReturn(1000L);
            byte[] jpgMagic = new byte[]{(byte)0xFF, (byte)0xD8, (byte)0xFF, (byte)0xE0};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(jpgMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/ProductAdmin.jsp")).thenReturn(dispatcher);
            
            try (MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(info);
                    });
                 MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        when(mock.doRetrieveByName(anyString())).thenReturn(product);
                    });
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(mockPart).write(anyString());
            }
        }
    }
}
