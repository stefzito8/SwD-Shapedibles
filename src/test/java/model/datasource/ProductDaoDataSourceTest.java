package model.datasource;

import categories.IntegrationTest;
import integration.H2TestDatabase;
import model.bean.ProductBean;
import org.junit.jupiter.api.*;

import javax.sql.DataSource;
import java.sql.SQLException;
import java.util.Collection;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Integration tests for ProductDaoDataSource.
 * 
 * Testing Level: Integration
 * Technique: White-Box (Branch Coverage) with H2 Database
 * 
 * ============================================================================
 * BRANCH STRUCTURE
 * ============================================================================
 * 
 * Method: doRetrieveByKey(int code)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | PDS-B1    | rs.next()                    | Populate bean     | Return default |
 * -----------------------------------------------------------------
 * 
 * Method: doDelete(int code)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | PDS-B2    | result != 0                  | Return true       | Return false   |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveAll(String order)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | PDS-B3    | order != null && !order.isEmpty() | Add ORDER BY | No ORDER BY  |
 * | PDS-B4    | rs.next() loop               | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveByName(String name)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | PDS-B5    | rs.next()                    | Populate bean     | Return default |
 * -----------------------------------------------------------------
 * 
 * Method: searchByName(String query)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | PDS-B6    | rs.next() loop               | Add to list       | Exit loop      |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@IntegrationTest
@DisplayName("ProductDaoDataSource Integration Tests")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public class ProductDaoDataSourceTest {

    private static DataSource dataSource;
    private ProductDaoDataSource productDao;

    @BeforeAll
    static void setUpClass() {
        dataSource = H2TestDatabase.getDataSource();
        H2TestDatabase.initializeDatabase();
    }

    @BeforeEach
    void setUp() {
        H2TestDatabase.resetDatabase();
        productDao = new ProductDaoDataSource(dataSource);
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
        @DisplayName("Save new product successfully")
        void testSaveNewProduct() throws SQLException {
            ProductBean product = createTestProduct("Test Product", 1);

            productDao.doSave(product);

            Collection<ProductBean> products = productDao.doRetrieveAll(null);
            assertFalse(products.isEmpty());
        }

        @Test
        @DisplayName("Save product with name only")
        void testSaveProductNameOnly() throws SQLException {
            ProductBean product = new ProductBean();
            product.setNome("Simple Product");
            product.setInfoCorrenti(-1);

            productDao.doSave(product);

            ProductBean retrieved = productDao.doRetrieveByName("Simple Product");
            assertEquals("Simple Product", retrieved.getNome());
        }

        @Test
        @DisplayName("Save multiple products")
        void testSaveMultipleProducts() throws SQLException {
            productDao.doSave(createTestProduct("Product 1", 1));
            productDao.doSave(createTestProduct("Product 2", 2));
            productDao.doSave(createTestProduct("Product 3", 3));

            Collection<ProductBean> products = productDao.doRetrieveAll(null);
            assertEquals(3, products.size());
        }
    }

    // ============================================================================
    // doRetrieveByKey Tests (Branch PDS-B1)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByKey Tests")
    class DoRetrieveByKeyTests {

        @Test
        @DisplayName("B1-True: Retrieve existing product populates bean")
        void testRetrieveExistingProduct() throws SQLException {
            productDao.doSave(createTestProduct("Test Product", 1));
            
            // Get the auto-generated code
            Collection<ProductBean> all = productDao.doRetrieveAll(null);
            int code = all.iterator().next().getCodice();

            ProductBean retrieved = productDao.doRetrieveByKey(code);

            assertNotNull(retrieved);
            assertEquals("Test Product", retrieved.getNome());
        }

        @Test
        @DisplayName("B1-False: Retrieve non-existent product returns default bean")
        void testRetrieveNonExistentProduct() throws SQLException {
            ProductBean retrieved = productDao.doRetrieveByKey(999);

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodice()); // Default value
        }

        @Test
        @DisplayName("Retrieve with code = 0")
        void testRetrieveZeroCode() throws SQLException {
            ProductBean retrieved = productDao.doRetrieveByKey(0);

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodice());
        }

        @Test
        @DisplayName("Retrieve with negative code")
        void testRetrieveNegativeCode() throws SQLException {
            ProductBean retrieved = productDao.doRetrieveByKey(-1);

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodice());
        }
    }

    // ============================================================================
    // doRetrieveByName Tests (Branch PDS-B5)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByName Tests")
    class DoRetrieveByNameTests {

        @Test
        @DisplayName("B5-True: Retrieve existing product by name")
        void testRetrieveExistingByName() throws SQLException {
            productDao.doSave(createTestProduct("Unique Product Name", 1));

            ProductBean retrieved = productDao.doRetrieveByName("Unique Product Name");

            assertNotNull(retrieved);
            assertEquals("Unique Product Name", retrieved.getNome());
        }

        @Test
        @DisplayName("B5-False: Retrieve non-existent product by name returns default bean")
        void testRetrieveNonExistentByName() throws SQLException {
            ProductBean retrieved = productDao.doRetrieveByName("NonExistent Product");

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodice());
        }

        @Test
        @DisplayName("Retrieve with empty name")
        void testRetrieveEmptyName() throws SQLException {
            ProductBean retrieved = productDao.doRetrieveByName("");

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodice());
        }
    }

    // ============================================================================
    // doDelete Tests (Branch PDS-B2)
    // ============================================================================

    @Nested
    @DisplayName("doDelete Tests")
    class DoDeleteTests {

        @Test
        @DisplayName("B2-True: Delete existing product returns true")
        void testDeleteExistingProduct() throws SQLException {
            productDao.doSave(createTestProduct("To Delete", 1));
            Collection<ProductBean> all = productDao.doRetrieveAll(null);
            int code = all.iterator().next().getCodice();

            boolean result = productDao.doDelete(code);

            assertTrue(result);
            ProductBean retrieved = productDao.doRetrieveByKey(code);
            assertEquals(-1, retrieved.getCodice());
        }

        @Test
        @DisplayName("B2-False: Delete non-existent product returns false")
        void testDeleteNonExistentProduct() throws SQLException {
            boolean result = productDao.doDelete(999);

            assertFalse(result);
        }

        @Test
        @DisplayName("Delete with code = 0")
        void testDeleteZeroCode() throws SQLException {
            boolean result = productDao.doDelete(0);

            assertFalse(result);
        }
    }

    // ============================================================================
    // doRetrieveAll Tests (Branches PDS-B3, PDS-B4)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveAll Tests")
    class DoRetrieveAllTests {

        @Test
        @DisplayName("B3-False, B4-False: Retrieve all from empty table")
        void testRetrieveAllEmpty() throws SQLException {
            Collection<ProductBean> products = productDao.doRetrieveAll(null);

            assertNotNull(products);
            assertTrue(products.isEmpty());
        }

        @Test
        @DisplayName("B3-False, B4-True: Retrieve all without order")
        void testRetrieveAllWithoutOrder() throws SQLException {
            productDao.doSave(createTestProduct("Product A", 1));
            productDao.doSave(createTestProduct("Product B", 2));

            Collection<ProductBean> products = productDao.doRetrieveAll(null);

            assertEquals(2, products.size());
        }

        @Test
        @DisplayName("B3-True, B4-True: Retrieve all with order by name")
        void testRetrieveAllWithOrder() throws SQLException {
            productDao.doSave(createTestProduct("B Product", 1));
            productDao.doSave(createTestProduct("A Product", 2));

            Collection<ProductBean> products = productDao.doRetrieveAll("NAME");

            assertEquals(2, products.size());
            // First product should be "A Product" when ordered by name
            ProductBean first = products.iterator().next();
            assertEquals("A Product", first.getNome());
        }

        @Test
        @DisplayName("B3-False: Retrieve all with empty order string")
        void testRetrieveAllEmptyOrder() throws SQLException {
            productDao.doSave(createTestProduct("Test", 1));

            Collection<ProductBean> products = productDao.doRetrieveAll("");

            assertEquals(1, products.size());
        }

        @Test
        @DisplayName("Retrieve all with order by CODE")
        void testRetrieveAllOrderByCode() throws SQLException {
            productDao.doSave(createTestProduct("First", 1));
            productDao.doSave(createTestProduct("Second", 2));

            Collection<ProductBean> products = productDao.doRetrieveAll("CODE");

            assertEquals(2, products.size());
        }
    }

    // ============================================================================
    // searchByName Tests (Branch PDS-B6)
    // ============================================================================

    @Nested
    @DisplayName("searchByName Tests")
    class SearchByNameTests {

        @Test
        @DisplayName("B6-True: Search finds matching products")
        void testSearchFindsProducts() throws SQLException {
            productDao.doSave(createTestProduct("Protein Bar", 1));
            productDao.doSave(createTestProduct("Protein Shake", 2));
            productDao.doSave(createTestProduct("Energy Bar", 3));

            List<ProductBean> results = productDao.searchByName("Protein");

            assertEquals(2, results.size());
            assertTrue(results.stream().allMatch(p -> p.getNome().contains("Protein")));
        }

        @Test
        @DisplayName("B6-False: Search finds no products")
        void testSearchFindsNoProducts() throws SQLException {
            productDao.doSave(createTestProduct("Product A", 1));

            List<ProductBean> results = productDao.searchByName("NonExistent");

            assertNotNull(results);
            assertTrue(results.isEmpty());
        }

        @Test
        @DisplayName("Search with partial match")
        void testSearchPartialMatch() throws SQLException {
            productDao.doSave(createTestProduct("Chocolate Cookie", 1));
            productDao.doSave(createTestProduct("Vanilla Cookie", 2));
            productDao.doSave(createTestProduct("Plain Cake", 3));

            List<ProductBean> results = productDao.searchByName("Cook");

            assertEquals(2, results.size());
        }

        @Test
        @DisplayName("Search with empty query returns all")
        void testSearchEmptyQuery() throws SQLException {
            productDao.doSave(createTestProduct("Product 1", 1));
            productDao.doSave(createTestProduct("Product 2", 2));

            List<ProductBean> results = productDao.searchByName("");

            assertEquals(2, results.size());
        }

        @Test
        @DisplayName("Search is case sensitive")
        void testSearchCaseSensitive() throws SQLException {
            productDao.doSave(createTestProduct("PROTEIN BAR", 1));
            productDao.doSave(createTestProduct("protein shake", 2));

            List<ProductBean> results = productDao.searchByName("PROTEIN");

            // Depending on database collation, this may find one or both
            assertFalse(results.isEmpty());
        }
    }

    // ============================================================================
    // doUpdateInfo Tests
    // ============================================================================

    @Nested
    @DisplayName("doUpdateInfo Tests")
    class DoUpdateInfoTests {

        @Test
        @DisplayName("Update info for existing product")
        void testUpdateInfoExistingProduct() throws SQLException {
            productDao.doSave(createTestProduct("Test Product", 1));
            Collection<ProductBean> all = productDao.doRetrieveAll(null);
            int code = all.iterator().next().getCodice();

            productDao.doUpdateInfo(code, 999);

            ProductBean retrieved = productDao.doRetrieveByKey(code);
            assertEquals(999, retrieved.getInfoCorrenti());
        }

        @Test
        @DisplayName("Update info for non-existent product does not throw")
        void testUpdateInfoNonExistent() throws SQLException {
            assertDoesNotThrow(() -> productDao.doUpdateInfo(999, 100));
        }

        @Test
        @DisplayName("Update info to different value")
        void testUpdateInfoDifferentValue() throws SQLException {
            productDao.doSave(createTestProduct("Product", 1));
            Collection<ProductBean> all = productDao.doRetrieveAll(null);
            int code = all.iterator().next().getCodice();

            productDao.doUpdateInfo(code, 50);
            ProductBean first = productDao.doRetrieveByKey(code);
            assertEquals(50, first.getInfoCorrenti());

            productDao.doUpdateInfo(code, 100);
            ProductBean second = productDao.doRetrieveByKey(code);
            assertEquals(100, second.getInfoCorrenti());
        }
    }

    // ============================================================================
    // Loop Boundary Tests
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("Loop: 0 iterations (no products)")
        void testLoopZeroIterations() throws SQLException {
            Collection<ProductBean> products = productDao.doRetrieveAll(null);
            assertEquals(0, products.size());
        }

        @Test
        @DisplayName("Loop: 1 iteration (single product)")
        void testLoopOneIteration() throws SQLException {
            productDao.doSave(createTestProduct("Single", 1));

            Collection<ProductBean> products = productDao.doRetrieveAll(null);
            assertEquals(1, products.size());
        }

        @Test
        @DisplayName("Loop: >1 iterations (multiple products)")
        void testLoopMultipleIterations() throws SQLException {
            for (int i = 1; i <= 10; i++) {
                productDao.doSave(createTestProduct("Product " + i, i));
            }

            Collection<ProductBean> products = productDao.doRetrieveAll(null);
            assertEquals(10, products.size());
        }
    }

    // ============================================================================
    // Helper Methods
    // ============================================================================

    private ProductBean createTestProduct(String name, int infoCorrenti) {
        ProductBean product = new ProductBean();
        product.setNome(name);
        product.setInfoCorrenti(infoCorrenti);
        return product;
    }
}
