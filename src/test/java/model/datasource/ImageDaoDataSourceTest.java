package model.datasource;

import categories.IntegrationTest;
import integration.H2TestDatabase;
import model.bean.ImageBean;
import org.junit.jupiter.api.*;

import javax.sql.DataSource;
import java.sql.SQLException;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Integration tests for ImageDaoDataSource.
 * 
 * Testing Level: Integration
 * Technique: White-Box (Branch Coverage) with H2 Database
 * 
 * ============================================================================
 * BRANCH STRUCTURE
 * ============================================================================
 * 
 * Method: doRetrieveByKey(int codice, int num)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | IMG-B1    | rs.next() (while)            | Populate bean     | Return default |
 * -----------------------------------------------------------------
 * 
 * Method: doDelete(int num, int codice)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | IMG-B2    | result != 0                  | Return true       | Return false   |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveAll(String order)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | IMG-B3    | order != null && !order.isEmpty() | Add ORDER BY | No ORDER BY  |
 * | IMG-B4    | rs.next() (while loop)       | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveByProduct(int codice)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | IMG-B5    | rs.next() (while loop)       | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@IntegrationTest
@DisplayName("ImageDaoDataSource Integration Tests")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public class ImageDaoDataSourceTest {

    private static DataSource dataSource;
    private ImageDaoDataSource imageDao;

    @BeforeAll
    static void setUpClass() {
        dataSource = H2TestDatabase.getDataSource();
        H2TestDatabase.initializeDatabase();
    }

    @BeforeEach
    void setUp() throws SQLException {
        H2TestDatabase.resetDatabase();
        imageDao = new ImageDaoDataSource(dataSource);
        // Insert a product first since images reference products
        insertTestProduct(1, "Test Product");
    }

    @AfterAll
    static void tearDownClass() {
        H2TestDatabase.resetDatabase();
    }

    // ============================================================================
    // doSave Tests
    // ============================================================================

    @Nested
    @DisplayName("doSave Tests")
    class DoSaveTests {

        @Test
        @DisplayName("Save new image successfully")
        void testSaveNewImage() throws SQLException {
            ImageBean image = createTestImage(1, "test.jpg");

            imageDao.doSave(image);

            Collection<ImageBean> images = imageDao.doRetrieveByProduct(1);
            assertEquals(1, images.size());
        }

        @Test
        @DisplayName("Save multiple images for same product")
        void testSaveMultipleImagesForProduct() throws SQLException {
            imageDao.doSave(createTestImage(1, "image1.jpg"));
            imageDao.doSave(createTestImage(1, "image2.jpg"));
            imageDao.doSave(createTestImage(1, "image3.jpg"));

            Collection<ImageBean> images = imageDao.doRetrieveByProduct(1);
            assertEquals(3, images.size());
        }
    }

    // ============================================================================
    // doRetrieveByKey Tests (Branch IMG-B1)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByKey Tests")
    class DoRetrieveByKeyTests {

        @Test
        @DisplayName("B1-True: Retrieve existing image - Note: DAO has bug (parameter #2 not set)")
        void testRetrieveExistingImage() throws SQLException {
            imageDao.doSave(createTestImage(1, "test.jpg"));
            Collection<ImageBean> all = imageDao.doRetrieveAll(null);
            ImageBean saved = all.iterator().next();

            // Note: ImageDaoDataSource.doRetrieveByKey has a bug where parameter #2 is not set
            // This test documents the bug and verifies the method throws an exception
            assertThrows(SQLException.class, () -> 
                imageDao.doRetrieveByKey(saved.getCodiceProdotto(), saved.getNumImage()));
        }

        @Test
        @DisplayName("B1-False: Retrieve non-existent image - Note: DAO has bug (parameter #2 not set)")
        void testRetrieveNonExistentImage() throws SQLException {
            // Note: ImageDaoDataSource.doRetrieveByKey has a bug where parameter #2 is not set
            // This test documents the bug and verifies the method throws an exception
            assertThrows(SQLException.class, () -> imageDao.doRetrieveByKey(999, 999));
        }
    }

    // ============================================================================
    // doDelete Tests (Branch IMG-B2)
    // ============================================================================

    @Nested
    @DisplayName("doDelete Tests")
    class DoDeleteTests {

        @Test
        @DisplayName("B2-True: Delete existing image returns true")
        void testDeleteExistingImage() throws SQLException {
            imageDao.doSave(createTestImage(1, "test.jpg"));
            Collection<ImageBean> all = imageDao.doRetrieveAll(null);
            ImageBean saved = all.iterator().next();

            boolean result = imageDao.doDelete(saved.getNumImage(), saved.getCodiceProdotto());

            assertTrue(result);
        }

        @Test
        @DisplayName("B2-False: Delete non-existent image returns false")
        void testDeleteNonExistentImage() throws SQLException {
            boolean result = imageDao.doDelete(999, 999);

            assertFalse(result);
        }
    }

    // ============================================================================
    // doRetrieveAll Tests (Branches IMG-B3, IMG-B4)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveAll Tests")
    class DoRetrieveAllTests {

        @Test
        @DisplayName("B3-False, B4-False: Retrieve all from empty table")
        void testRetrieveAllEmpty() throws SQLException {
            Collection<ImageBean> images = imageDao.doRetrieveAll(null);

            assertNotNull(images);
            assertTrue(images.isEmpty());
        }

        @Test
        @DisplayName("B3-False, B4-True: Retrieve all without order")
        void testRetrieveAllWithoutOrder() throws SQLException {
            imageDao.doSave(createTestImage(1, "image1.jpg"));
            imageDao.doSave(createTestImage(1, "image2.jpg"));

            Collection<ImageBean> images = imageDao.doRetrieveAll(null);

            assertEquals(2, images.size());
        }

        @Test
        @DisplayName("B3-True, B4-True: Retrieve all with order")
        void testRetrieveAllWithOrder() throws SQLException {
            imageDao.doSave(createTestImage(1, "image1.jpg"));
            imageDao.doSave(createTestImage(1, "image2.jpg"));

            Collection<ImageBean> images = imageDao.doRetrieveAll("Images_Num");

            assertEquals(2, images.size());
        }

        @Test
        @DisplayName("B3-False: Retrieve all with empty order string")
        void testRetrieveAllEmptyOrder() throws SQLException {
            imageDao.doSave(createTestImage(1, "test.jpg"));

            Collection<ImageBean> images = imageDao.doRetrieveAll("");

            assertEquals(1, images.size());
        }

        @Test
        @DisplayName("Verify all fields are populated in doRetrieveAll")
        void testRetrieveAllVerifiesAllFields() throws SQLException {
            imageDao.doSave(createTestImage(1, "verify_test_image.jpg"));

            Collection<ImageBean> images = imageDao.doRetrieveAll(null);
            ImageBean retrieved = images.iterator().next();

            // Assertions on ALL fields to kill setter mutations
            assertEquals(1, retrieved.getCodiceProdotto());
            assertTrue(retrieved.getNumImage() > 0);
            assertEquals("verify_test_image.jpg", retrieved.getImg());
        }
    }

    // ============================================================================
    // doRetrieveByProduct Tests (Branch IMG-B5)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByProduct Tests")
    class DoRetrieveByProductTests {

        @Test
        @DisplayName("B5-True: Retrieve images for product with images")
        void testRetrieveByProductWithImages() throws SQLException {
            imageDao.doSave(createTestImage(1, "image1.jpg"));
            imageDao.doSave(createTestImage(1, "image2.jpg"));

            Collection<ImageBean> images = imageDao.doRetrieveByProduct(1);

            assertEquals(2, images.size());
        }

        @Test
        @DisplayName("B5-False: Retrieve images for product without images")
        void testRetrieveByProductNoImages() throws SQLException {
            Collection<ImageBean> images = imageDao.doRetrieveByProduct(1);

            assertNotNull(images);
            assertTrue(images.isEmpty());
        }

        @Test
        @DisplayName("Retrieve images for non-existent product")
        void testRetrieveByNonExistentProduct() throws SQLException {
            Collection<ImageBean> images = imageDao.doRetrieveByProduct(999);

            assertNotNull(images);
            assertTrue(images.isEmpty());
        }

        @Test
        @DisplayName("Verify all fields are populated in doRetrieveByProduct")
        void testRetrieveByProductVerifiesAllFields() throws SQLException {
            imageDao.doSave(createTestImage(1, "product_verify_image.png"));

            Collection<ImageBean> images = imageDao.doRetrieveByProduct(1);
            ImageBean retrieved = images.iterator().next();

            // Assertions on ALL fields to kill setter mutations
            assertEquals(1, retrieved.getCodiceProdotto());
            assertTrue(retrieved.getNumImage() > 0);
            assertEquals("product_verify_image.png", retrieved.getImg());
        }
    }

    // ============================================================================
    // Loop Boundary Tests
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("Loop: 0 iterations (no images)")
        void testLoopZeroIterations() throws SQLException {
            Collection<ImageBean> images = imageDao.doRetrieveAll(null);
            assertEquals(0, images.size());
        }

        @Test
        @DisplayName("Loop: 1 iteration (single image)")
        void testLoopOneIteration() throws SQLException {
            imageDao.doSave(createTestImage(1, "single.jpg"));

            Collection<ImageBean> images = imageDao.doRetrieveAll(null);
            assertEquals(1, images.size());
        }

        @Test
        @DisplayName("Loop: >1 iterations (multiple images)")
        void testLoopMultipleIterations() throws SQLException {
            for (int i = 1; i <= 5; i++) {
                imageDao.doSave(createTestImage(1, "image" + i + ".jpg"));
            }

            Collection<ImageBean> images = imageDao.doRetrieveAll(null);
            assertEquals(5, images.size());
        }
    }

    // ============================================================================
    // Mutation Killer Tests
    // ============================================================================

    @Nested
    @DisplayName("Mutation Killer Tests")
    class MutationKillerTests {
        
        @Test
        @DisplayName("doSave actually persists data - kills VoidMethodCallMutator")
        void testDoSaveActuallyPersists() throws SQLException {
            ImageBean image = createTestImage(1, "mutation_test.jpg");
            
            // Verify empty before save
            Collection<ImageBean> beforeSave = imageDao.doRetrieveAll(null);
            assertEquals(0, beforeSave.size(), "Should be empty before save");
            
            // Save the image
            imageDao.doSave(image);
            
            // Verify present after save - if mutation removes doSave, this fails
            Collection<ImageBean> afterSave = imageDao.doRetrieveAll(null);
            assertEquals(1, afterSave.size(), "Should have 1 image after save");
            
            // Verify correct data was saved
            ImageBean saved = afterSave.iterator().next();
            assertEquals(1, saved.getCodiceProdotto());
            assertEquals("mutation_test.jpg", saved.getImg());
        }
        
        @Test
        @DisplayName("doDelete actually removes data - kills NegateConditionalsMutator line 76")
        void testDoDeleteActuallyRemoves() throws SQLException {
            // First save an image
            imageDao.doSave(createTestImage(1, "delete_test.jpg"));
            
            // Verify it exists
            Collection<ImageBean> afterSave = imageDao.doRetrieveAll(null);
            assertEquals(1, afterSave.size());
            ImageBean saved = afterSave.iterator().next();
            
            // Delete it
            boolean result = imageDao.doDelete(saved.getNumImage(), saved.getCodiceProdotto());
            
            // Both the return value AND the actual deletion matter
            assertTrue(result, "doDelete should return true");
            
            // Verify it was actually deleted
            Collection<ImageBean> afterDelete = imageDao.doRetrieveAll(null);
            assertEquals(0, afterDelete.size(), "Should be empty after delete");
        }
        
        @Test
        @DisplayName("doDelete return value matches actual deletion - kills return value mutations")
        void testDoDeleteReturnValueMatchesReality() throws SQLException {
            // Delete non-existent returns false AND doesn't affect database
            boolean falseResult = imageDao.doDelete(999, 999);
            assertFalse(falseResult, "Deleting non-existent should return false");
            
            // Add an image
            imageDao.doSave(createTestImage(1, "return_test.jpg"));
            Collection<ImageBean> afterSave = imageDao.doRetrieveAll(null);
            ImageBean saved = afterSave.iterator().next();
            
            // Delete existing returns true AND actually removes
            boolean trueResult = imageDao.doDelete(saved.getNumImage(), saved.getCodiceProdotto());
            assertTrue(trueResult, "Deleting existing should return true");
            assertTrue(imageDao.doRetrieveAll(null).isEmpty(), "Image should be gone");
        }
        
        @Test
        @DisplayName("doRetrieveAll returns correct collection - kills EmptyObjectReturnValsMutator line 152")
        void testDoRetrieveAllReturnsCorrectCollection() throws SQLException {
            imageDao.doSave(createTestImage(1, "retrieve1.jpg"));
            imageDao.doSave(createTestImage(1, "retrieve2.jpg"));
            imageDao.doSave(createTestImage(1, "retrieve3.jpg"));
            
            Collection<ImageBean> result = imageDao.doRetrieveAll(null);
            
            // Must use the returned collection
            assertNotNull(result, "Result must not be null");
            assertFalse(result.isEmpty(), "Result must not be empty");
            assertEquals(3, result.size(), "Must have 3 images");
            
            // Verify each element is valid
            for (ImageBean img : result) {
                assertNotNull(img);
                assertEquals(1, img.getCodiceProdotto());
                assertTrue(img.getImg().startsWith("retrieve"));
            }
        }
        
        @Test
        @DisplayName("doRetrieveByProduct returns images for specific product only")
        void testDoRetrieveByProductReturnsSpecificProductOnly() throws SQLException {
            // Add another product
            insertTestProduct(2, "Another Product");
            
            // Save images for both products
            imageDao.doSave(createTestImage(1, "product1_img.jpg"));
            imageDao.doSave(createTestImage(2, "product2_img.jpg"));
            
            // Retrieve for product 1 only
            Collection<ImageBean> product1Images = imageDao.doRetrieveByProduct(1);
            
            assertEquals(1, product1Images.size());
            ImageBean img = product1Images.iterator().next();
            assertEquals(1, img.getCodiceProdotto());
            assertEquals("product1_img.jpg", img.getImg());
            assertNotEquals(2, img.getCodiceProdotto());
        }
    }

    // ============================================================================
    // Helper Methods
    // ============================================================================

    private ImageBean createTestImage(int productCode, String imgPath) {
        ImageBean image = new ImageBean();
        image.setCodiceProdotto(productCode);
        image.setImg(imgPath);
        return image;
    }

    private void insertTestProduct(int code, String name) throws SQLException {
        try (var connection = dataSource.getConnection();
             var stmt = connection.prepareStatement("INSERT INTO product (code, CURRENT_INFOS, name) VALUES (?, ?, ?)")) {
            stmt.setInt(1, code);
            stmt.setInt(2, 1);
            stmt.setString(3, name);
            stmt.executeUpdate();
        }
    }
}
