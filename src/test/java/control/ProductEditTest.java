package control;

import categories.UnitTest;
import model.bean.ImageBean;
import model.bean.InfoBean;
import model.bean.NutritionTableBean;
import model.bean.ProductBean;
import model.datasource.ImageDaoDataSource;
import model.datasource.InfoDaoDataSource;
import model.datasource.NutritionTableDaoDataSource;
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

import org.mockito.ArgumentCaptor;

/**
 * Unit tests for ProductEdit controller.
 * 
 * Testing Level: Unit
 * Technique: White-Box (Statement Testing, Branch Testing) with Mocking
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@DisplayName("ProductEdit Controller Tests")
public class ProductEditTest {
    
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
    private Part mockPart;
    
    private ProductEdit servlet;
    
    @BeforeEach
    void setUp() throws Exception {
        servlet = new ProductEdit() {
            @Override
            public ServletContext getServletContext() {
                return servletContext;
            }
        };
        
        when(request.getServletContext()).thenReturn(servletContext);
        when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
        when(servletContext.getRealPath("")).thenReturn("C:\\test\\webapp\\");
    }
    
    @Nested
    @DisplayName("doGet Tests")
    class DoGetTests {
        
        @Test
        @DisplayName("doGet delegates to doPost")
        void testDoGetDelegatesToDoPost() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productEdit.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setNome("Test Product");
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        InfoBean info = new InfoBean();
                        info.setCodice(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(info);
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(1)).thenReturn(new NutritionTableBean()))) {
                
                servlet.doGet(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
    }
    
    @Nested
    @DisplayName("View Mode Tests")
    class ViewModeTests {
        
        @Test
        @DisplayName("View mode loads product data and forwards to edit page")
        void testViewModeLoadsProductData() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productEdit.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(1)).thenReturn(new InfoBean()));
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(1)).thenReturn(new NutritionTableBean()))) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute(eq("productE"), any(ProductBean.class));
                verify(request).setAttribute(eq("infoE"), any(InfoBean.class));
                verify(request).setAttribute(eq("nutritionTableE"), any(NutritionTableBean.class));
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("View mode with 'view' action also shows edit page")
        void testViewModeWithViewAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("view");
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productEdit.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean()));
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()))) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
    }
    
    @Nested
    @DisplayName("Edit Action Tests")
    class EditActionTests {
        
        @BeforeEach
        void setUpEditAction() {
            when(request.getParameter("action")).thenReturn("edit");
            when(request.getParameter("product")).thenReturn("1");
            when(request.getParameter("name")).thenReturn("Updated Product");
            when(request.getParameter("description")).thenReturn("Updated description");
            when(request.getParameter("price")).thenReturn("29.99");
            when(request.getParameter("quantity")).thenReturn("100");
            when(request.getParameter("type")).thenReturn("Category A");
            when(request.getParameter("cal")).thenReturn("200");
            when(request.getParameter("fats")).thenReturn("10.0");
            when(request.getParameter("satFats")).thenReturn("3.0");
            when(request.getParameter("carbs")).thenReturn("25.0");
            when(request.getParameter("sugars")).thenReturn("5.0");
            when(request.getParameter("fibers")).thenReturn("2.0");
            when(request.getParameter("protein")).thenReturn("8.0");
            when(request.getParameter("salt")).thenReturn("0.5");
        }
        
        @Test
        @DisplayName("Edit action updates product info and forwards to admin page")
        void testEditActionUpdatesProduct() throws ServletException, IOException, SQLException {
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            when(request.getParts()).thenReturn(Collections.emptyList());
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        InfoBean newInfo = new InfoBean();
                        newInfo.setCodice(2);
                        when(mock.doRetrieveByName("Updated Product")).thenReturn(newInfo);
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(anyInt())).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                // Verify DAO operations to kill VoidMethodCallMutator mutations
                // Use ArgumentCaptor to verify InfoBean properties were set correctly (kills setter mutations lines 125-129)
                ArgumentCaptor<InfoBean> infoBeanCaptor = ArgumentCaptor.forClass(InfoBean.class);
                verify(infoDaoMock.constructed().get(0)).doSave(infoBeanCaptor.capture());
                InfoBean capturedInfo = infoBeanCaptor.getValue();
                assertEquals("Updated Product", capturedInfo.getNome());
                assertEquals("Updated description", capturedInfo.getDescrizione());
                assertEquals(29.99, capturedInfo.getCosto(), 0.01);
                assertEquals(100, capturedInfo.getDisponibilità());
                assertEquals("Category A", capturedInfo.getTipologia());
                
                verify(prodDaoMock.constructed().get(0)).doUpdateInfo(eq(1), anyInt());
                verify(nutDaoMock.constructed().get(0)).doDelete(1);
                
                // Use ArgumentCaptor to verify NutritionTableBean properties were set correctly (kills setter mutations lines 137-145)
                ArgumentCaptor<NutritionTableBean> nutBeanCaptor = ArgumentCaptor.forClass(NutritionTableBean.class);
                verify(nutDaoMock.constructed().get(0)).doSave(nutBeanCaptor.capture());
                NutritionTableBean capturedNut = nutBeanCaptor.getValue();
                assertEquals(1, capturedNut.getCodiceProdotto());
                assertEquals(200, capturedNut.getEnergia());
                assertEquals(10.0, capturedNut.getGrassi(), 0.01);
                assertEquals(3.0, capturedNut.getGrassiSaturi(), 0.01);
                assertEquals(25.0, capturedNut.getCarboedrati(), 0.01);
                assertEquals(5.0, capturedNut.getZucherri(), 0.01);
                assertEquals(2.0, capturedNut.getFibre(), 0.01);
                assertEquals(8.0, capturedNut.getProteine(), 0.01);
                assertEquals(0.5, capturedNut.getSale(), 0.01);
                
                // Verify request attribute operations
                verify(request).removeAttribute("productE");
                verify(request).setAttribute(eq("productE"), any(ProductBean.class));
                verify(request).removeAttribute("infoE");
                verify(request).setAttribute(eq("infoE"), any(InfoBean.class));
                verify(request).removeAttribute("nutritionTableE");
                verify(request).setAttribute(eq("nutritionTableE"), any(NutritionTableBean.class));
                
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Edit action saves nutrition data")
        void testEditActionSavesNutritionData() throws ServletException, IOException, SQLException {
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            when(request.getParts()).thenReturn(Collections.emptyList());
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        InfoBean newInfo = new InfoBean();
                        newInfo.setCodice(2);
                        when(mock.doRetrieveByName(anyString())).thenReturn(newInfo);
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(anyInt())).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                assertFalse(nutDaoMock.constructed().isEmpty());
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Edit action deletes old images")
        void testEditActionUpdatesImages() throws ServletException, IOException, SQLException {
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            when(request.getParts()).thenReturn(Collections.emptyList());
            
            Collection<ImageBean> existingImages = new ArrayList<>();
            ImageBean img1 = new ImageBean();
            img1.setNumImage(1);
            img1.setCodiceProdotto(1);
            existingImages.add(img1);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        when(mock.doRetrieveByName(anyString())).thenReturn(new InfoBean());
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(1)).thenReturn(existingImages))) {
                
                servlet.doPost(request, response);
                
                // Verify imgDao.doDelete is called for existing images (kills VoidMethodCallMutator mutations)
                verify(imgDaoMock.constructed().get(0)).doDelete(1, 1);
                
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Edit action saves new images with correct properties")
        void testEditActionSavesNewImages() throws ServletException, IOException, SQLException {
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            
            // Set up a mock file upload Part with valid JPG magic number
            Part mockPart = mock(Part.class);
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.jpg\"");
            when(mockPart.getSize()).thenReturn(1000L);
            // Use valid JPG magic number bytes so the file passes validation
            byte[] jpgMagic = new byte[]{(byte)0xFF, (byte)0xD8, (byte)0xFF, (byte)0xE0};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(jpgMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        InfoBean newInfo = new InfoBean();
                        newInfo.setCodice(2);
                        when(mock.doRetrieveByName(anyString())).thenReturn(newInfo);
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(anyInt())).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                // Use ArgumentCaptor to verify ImageBean properties were set correctly (kills setter mutations lines 160-162)
                ArgumentCaptor<ImageBean> imgBeanCaptor = ArgumentCaptor.forClass(ImageBean.class);
                verify(imgDaoMock.constructed().get(0)).doSave(imgBeanCaptor.capture());
                ImageBean capturedImg = imgBeanCaptor.getValue();
                assertEquals(1, capturedImg.getCodiceProdotto());
                assertEquals("test.jpg", capturedImg.getImg());
                
                verify(dispatcher).forward(request, response);
            }
        }
    }
    
    @Nested
    @DisplayName("File Upload Tests")
    class FileUploadTests {
        
        @BeforeEach
        void setUpEditWithFile() throws Exception {
            when(request.getParameter("action")).thenReturn("edit");
            when(request.getParameter("product")).thenReturn("1");
            when(request.getParameter("name")).thenReturn("Product");
            when(request.getParameter("description")).thenReturn("Description");
            when(request.getParameter("price")).thenReturn("10.0");
            when(request.getParameter("quantity")).thenReturn("10");
            when(request.getParameter("type")).thenReturn("Type");
            when(request.getParameter("cal")).thenReturn("100");
            when(request.getParameter("fats")).thenReturn("5.0");
            when(request.getParameter("satFats")).thenReturn("2.0");
            when(request.getParameter("carbs")).thenReturn("20.0");
            when(request.getParameter("sugars")).thenReturn("5.0");
            when(request.getParameter("fibers")).thenReturn("1.0");
            when(request.getParameter("protein")).thenReturn("5.0");
            when(request.getParameter("salt")).thenReturn("0.3");
        }
        
        @Test
        @DisplayName("Invalid file extension sets error attribute")
        void testInvalidFileExtensionSetsError() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.exe\"");
            lenient().when(mockPart.getSize()).thenReturn(1000L);
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        when(mock.doRetrieveByName(anyString())).thenReturn(new InfoBean());
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(anyInt())).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute(eq("error"), contains("estensione"));
            }
        }
        
        @Test
        @DisplayName("File too large sets error attribute")
        void testFileTooLargeSetsError() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.jpg\"");
            when(mockPart.getSize()).thenReturn(10 * 1024 * 1024L);
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        when(mock.doRetrieveByName(anyString())).thenReturn(new InfoBean());
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(anyInt())).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute(eq("error"), contains("taglia"));
            }
        }
        
        @Test
        @DisplayName("File at exact limit (5MB) is accepted - kills ConditionalsBoundaryMutator")
        void testFileAtExactLimitIsAccepted() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.jpg\"");
            // Exactly 5MB - this should be accepted (boundary test)
            when(mockPart.getSize()).thenReturn(5L * 1024 * 1024);
            byte[] jpgMagic = new byte[]{(byte)0xFF, (byte)0xD8, (byte)0xFF, (byte)0xE0};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(jpgMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        when(mock.doRetrieveByName(anyString())).thenReturn(new InfoBean());
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(anyInt())).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                // File at exactly 5MB should be accepted - verify write was called
                verify(mockPart).write(anyString());
                // Should NOT set the "taglia" error
                verify(request, never()).setAttribute(eq("error"), contains("taglia"));
            }
        }
        
        @Test
        @DisplayName("File one byte over limit (5MB + 1) is rejected - kills ConditionalsBoundaryMutator")
        void testFileOneByteOverLimitIsRejected() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.jpg\"");
            // 5MB + 1 byte - this should be rejected (boundary test)
            when(mockPart.getSize()).thenReturn(5L * 1024 * 1024 + 1);
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        when(mock.doRetrieveByName(anyString())).thenReturn(new InfoBean());
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(anyInt())).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                // File at 5MB + 1 should be rejected
                verify(request).setAttribute(eq("error"), contains("taglia"));
            }
        }
        
        @Test
        @DisplayName("Invalid magic number sets error attribute")
        void testInvalidMagicNumberSetsError() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.jpg\"");
            when(mockPart.getSize()).thenReturn(1000L);
            byte[] invalidMagic = new byte[]{0x00, 0x00, 0x00, 0x00};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(invalidMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        when(mock.doRetrieveByName(anyString())).thenReturn(new InfoBean());
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(anyInt())).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute(eq("error"), contains("magic number"));
            }
        }
        
        @Test
        @DisplayName("Valid JPG file is processed correctly")
        void testValidJpgFileIsProcessed() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.jpg\"");
            when(mockPart.getSize()).thenReturn(1000L);
            byte[] jpgMagic = new byte[]{(byte)0xFF, (byte)0xD8, (byte)0xFF, (byte)0xE0};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(jpgMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        when(mock.doRetrieveByName(anyString())).thenReturn(new InfoBean());
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(anyInt())).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                verify(mockPart).write(anyString());
            }
        }
        
        @Test
        @DisplayName("Valid PNG file is processed correctly")
        void testValidPngFileIsProcessed() throws ServletException, IOException, SQLException {
            when(mockPart.getHeader("content-disposition"))
                .thenReturn("form-data; name=\"file\"; filename=\"test.png\"");
            when(mockPart.getSize()).thenReturn(1000L);
            byte[] pngMagic = new byte[]{(byte)0x89, 'P', 'N', 'G'};
            when(mockPart.getInputStream()).thenReturn(new ByteArrayInputStream(pngMagic));
            when(request.getParts()).thenReturn(Collections.singletonList(mockPart));
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        when(mock.doRetrieveByName(anyString())).thenReturn(new InfoBean());
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(anyInt())).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                verify(mockPart).write(anyString());
            }
        }
    }
    
    @Nested
    @DisplayName("Exception Handling Tests")
    class ExceptionHandlingTests {
        
        @Test
        @DisplayName("SQLException sets error attribute")
        void testSqlExceptionSetsError() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("product")).thenReturn("1");
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productEdit.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenThrow(new SQLException("Database error"));
                    })) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute(eq("error"), anyString());
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("NumberFormatException during edit is handled")
        void testNumberFormatExceptionDuringEdit() throws ServletException, IOException {
            when(request.getParameter("action")).thenReturn("edit");
            when(request.getParameter("product")).thenReturn("invalid");
            lenient().when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productEdit.jsp"))
                .thenReturn(dispatcher);
            lenient().when(request.getParts()).thenReturn(Collections.emptyList());
            
            assertThrows(NumberFormatException.class, () -> servlet.doPost(request, response));
        }
    }
    
    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {
        
        @Test
        @DisplayName("Zero file parts - no file processing")
        void testZeroFileParts() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("edit");
            when(request.getParameter("product")).thenReturn("1");
            when(request.getParameter("name")).thenReturn("Product");
            when(request.getParameter("description")).thenReturn("Description");
            when(request.getParameter("price")).thenReturn("10.0");
            when(request.getParameter("quantity")).thenReturn("10");
            when(request.getParameter("type")).thenReturn("Type");
            when(request.getParameter("cal")).thenReturn("100");
            when(request.getParameter("fats")).thenReturn("5.0");
            when(request.getParameter("satFats")).thenReturn("2.0");
            when(request.getParameter("carbs")).thenReturn("20.0");
            when(request.getParameter("sugars")).thenReturn("5.0");
            when(request.getParameter("fibers")).thenReturn("1.0");
            when(request.getParameter("protein")).thenReturn("5.0");
            when(request.getParameter("salt")).thenReturn("0.3");
            
            when(request.getParts()).thenReturn(Collections.emptyList());
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        when(mock.doRetrieveByName(anyString())).thenReturn(new InfoBean());
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(anyInt())).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Multiple existing images - all are deleted")
        void testMultipleExistingImagesDeleted() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("edit");
            when(request.getParameter("product")).thenReturn("1");
            when(request.getParameter("name")).thenReturn("Product");
            when(request.getParameter("description")).thenReturn("Description");
            when(request.getParameter("price")).thenReturn("10.0");
            when(request.getParameter("quantity")).thenReturn("10");
            when(request.getParameter("type")).thenReturn("Type");
            when(request.getParameter("cal")).thenReturn("100");
            when(request.getParameter("fats")).thenReturn("5.0");
            when(request.getParameter("satFats")).thenReturn("2.0");
            when(request.getParameter("carbs")).thenReturn("20.0");
            when(request.getParameter("sugars")).thenReturn("5.0");
            when(request.getParameter("fibers")).thenReturn("1.0");
            when(request.getParameter("protein")).thenReturn("5.0");
            when(request.getParameter("salt")).thenReturn("0.3");
            
            when(request.getParts()).thenReturn(Collections.emptyList());
            when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/productAdmin.jsp"))
                .thenReturn(dispatcher);
            
            Collection<ImageBean> existingImages = new ArrayList<>();
            for (int i = 1; i <= 3; i++) {
                ImageBean img = new ImageBean();
                img.setNumImage(i);
                img.setCodiceProdotto(1);
                existingImages.add(img);
            }
            
            try (MockedConstruction<ProductDaoDataSource> prodDaoMock = mockConstruction(ProductDaoDataSource.class,
                    (mock, context) -> {
                        ProductBean product = new ProductBean();
                        product.setCodice(1);
                        product.setInfoCorrenti(1);
                        when(mock.doRetrieveByKey(1)).thenReturn(product);
                    });
                 MockedConstruction<InfoDaoDataSource> infoDaoMock = mockConstruction(InfoDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveByKey(anyInt())).thenReturn(new InfoBean());
                        when(mock.doRetrieveByName(anyString())).thenReturn(new InfoBean());
                    });
                 MockedConstruction<NutritionTableDaoDataSource> nutDaoMock = mockConstruction(NutritionTableDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByKey(anyInt())).thenReturn(new NutritionTableBean()));
                 MockedConstruction<ImageDaoDataSource> imgDaoMock = mockConstruction(ImageDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByProduct(1)).thenReturn(existingImages))) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
    }
}
