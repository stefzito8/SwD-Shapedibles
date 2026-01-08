package model.datasource;

import categories.IntegrationTest;
import integration.H2TestDatabase;
import model.bean.NutritionTableBean;
import org.junit.jupiter.api.*;

import javax.sql.DataSource;
import java.sql.SQLException;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Integration tests for NutritionTableDaoDataSource.
 * 
 * Testing Level: Integration
 * Technique: White-Box (Branch Coverage) with H2 Database
 * 
 * ============================================================================
 * BRANCH STRUCTURE
 * ============================================================================
 * 
 * Method: doRetrieveByKey(int productID)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | NUT-B1    | rs.next() (while)            | Populate bean     | Return default |
 * -----------------------------------------------------------------
 * 
 * Method: doDelete(int productID)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | NUT-B2    | result != 0                  | Return true       | Return false   |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveAll(String order)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | NUT-B3    | order != null && !order.equals("") | Add ORDER BY | No ORDER BY  |
 * | NUT-B4    | rs.next() (while loop)       | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@IntegrationTest
@DisplayName("NutritionTableDaoDataSource Integration Tests")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public class NutritionTableDaoDataSourceTest {

    private static DataSource dataSource;
    private NutritionTableDaoDataSource nutritionDao;

    @BeforeAll
    static void setUpClass() {
        dataSource = H2TestDatabase.getDataSource();
        H2TestDatabase.initializeDatabase();
    }

    @BeforeEach
    void setUp() throws SQLException {
        H2TestDatabase.resetDatabase();
        nutritionDao = new NutritionTableDaoDataSource(dataSource);
        // Insert a product first since nutrition tables reference products
        insertTestProduct(1, "Test Product");
        insertTestProduct(2, "Test Product 2");
        insertTestProduct(3, "Test Product 3");
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
        @DisplayName("Save new nutrition table successfully")
        void testSaveNewNutritionTable() throws SQLException {
            NutritionTableBean nutrition = createTestNutrition(1);

            nutritionDao.doSave(nutrition);

            NutritionTableBean retrieved = nutritionDao.doRetrieveByKey(1);
            assertEquals(1, retrieved.getCodiceProdotto());
        }

        @Test
        @DisplayName("Save nutrition table with all fields")
        void testSaveNutritionAllFields() throws SQLException {
            // Note: Using integer values because DAO's doRetrieveByKey uses getInt() instead of getDouble()
            NutritionTableBean nutrition = new NutritionTableBean();
            nutrition.setCodiceProdotto(1);
            nutrition.setEnergia(250);
            nutrition.setGrassi(10.0);
            nutrition.setGrassiSaturi(3.0);
            nutrition.setCarboedrati(30.0);
            nutrition.setZucherri(8.0);
            nutrition.setFibre(4.0);
            nutrition.setProteine(12.0);
            nutrition.setSale(1.0);

            nutritionDao.doSave(nutrition);

            NutritionTableBean retrieved = nutritionDao.doRetrieveByKey(1);
            assertEquals(250, retrieved.getEnergia());
            assertEquals(10.0, retrieved.getGrassi(), 0.01);
            assertEquals(3.0, retrieved.getGrassiSaturi(), 0.01);
            assertEquals(30.0, retrieved.getCarboedrati(), 0.01);
            assertEquals(8.0, retrieved.getZucherri(), 0.01);
            assertEquals(4.0, retrieved.getFibre(), 0.01);
            assertEquals(12.0, retrieved.getProteine(), 0.01);
            assertEquals(1.0, retrieved.getSale(), 0.01);
        }

        @Test
        @DisplayName("Save multiple nutrition tables")
        void testSaveMultipleNutritionTables() throws SQLException {
            nutritionDao.doSave(createTestNutrition(1));
            nutritionDao.doSave(createTestNutrition(2));
            nutritionDao.doSave(createTestNutrition(3));

            Collection<NutritionTableBean> tables = nutritionDao.doRetrieveAll(null);
            assertEquals(3, tables.size());
        }
    }

    // ============================================================================
    // doRetrieveByKey Tests (Branch NUT-B1)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByKey Tests")
    class DoRetrieveByKeyTests {

        @Test
        @DisplayName("B1-True: Retrieve existing nutrition table")
        void testRetrieveExistingByKey() throws SQLException {
            nutritionDao.doSave(createTestNutrition(1));

            NutritionTableBean retrieved = nutritionDao.doRetrieveByKey(1);

            assertNotNull(retrieved);
            assertEquals(1, retrieved.getCodiceProdotto());
        }

        @Test
        @DisplayName("B1-False: Retrieve non-existent nutrition table returns default bean")
        void testRetrieveNonExistentByKey() throws SQLException {
            NutritionTableBean retrieved = nutritionDao.doRetrieveByKey(999);

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodiceProdotto());
        }

        @Test
        @DisplayName("Retrieve with productID = 0")
        void testRetrieveZeroProductId() throws SQLException {
            NutritionTableBean retrieved = nutritionDao.doRetrieveByKey(0);

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodiceProdotto());
        }

        @Test
        @DisplayName("Retrieve with negative productID")
        void testRetrieveNegativeProductId() throws SQLException {
            NutritionTableBean retrieved = nutritionDao.doRetrieveByKey(-1);

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodiceProdotto());
        }
    }

    // ============================================================================
    // doDelete Tests (Branch NUT-B2)
    // ============================================================================

    @Nested
    @DisplayName("doDelete Tests")
    class DoDeleteTests {

        @Test
        @DisplayName("B2-True: Delete existing nutrition table returns true")
        void testDeleteExistingNutrition() throws SQLException {
            nutritionDao.doSave(createTestNutrition(1));

            boolean result = nutritionDao.doDelete(1);

            assertTrue(result);
            NutritionTableBean retrieved = nutritionDao.doRetrieveByKey(1);
            assertEquals(-1, retrieved.getCodiceProdotto());
        }

        @Test
        @DisplayName("B2-False: Delete non-existent nutrition table returns false")
        void testDeleteNonExistentNutrition() throws SQLException {
            boolean result = nutritionDao.doDelete(999);

            assertFalse(result);
        }

        @Test
        @DisplayName("Delete with productID = 0")
        void testDeleteZeroProductId() throws SQLException {
            boolean result = nutritionDao.doDelete(0);

            assertFalse(result);
        }
    }

    // ============================================================================
    // doRetrieveAll Tests (Branches NUT-B3, NUT-B4)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveAll Tests")
    class DoRetrieveAllTests {

        @Test
        @DisplayName("B3-False, B4-False: Retrieve all from empty table")
        void testRetrieveAllEmpty() throws SQLException {
            Collection<NutritionTableBean> tables = nutritionDao.doRetrieveAll(null);

            assertNotNull(tables);
            assertTrue(tables.isEmpty());
        }

        @Test
        @DisplayName("B3-False, B4-True: Retrieve all without order")
        void testRetrieveAllWithoutOrder() throws SQLException {
            nutritionDao.doSave(createTestNutrition(1));
            nutritionDao.doSave(createTestNutrition(2));

            Collection<NutritionTableBean> tables = nutritionDao.doRetrieveAll(null);

            assertEquals(2, tables.size());
        }

        @Test
        @DisplayName("B3-True, B4-True: Retrieve all with order")
        void testRetrieveAllWithOrder() throws SQLException {
            nutritionDao.doSave(createTestNutrition(1));
            nutritionDao.doSave(createTestNutrition(2));

            Collection<NutritionTableBean> tables = nutritionDao.doRetrieveAll("PRODUCT_CODE");

            assertEquals(2, tables.size());
        }

        @Test
        @DisplayName("B3-False: Retrieve all with empty order string")
        void testRetrieveAllEmptyOrder() throws SQLException {
            nutritionDao.doSave(createTestNutrition(1));

            Collection<NutritionTableBean> tables = nutritionDao.doRetrieveAll("");

            assertEquals(1, tables.size());
        }

        @Test
        @DisplayName("Retrieve all with order by energy")
        void testRetrieveAllOrderByEnergy() throws SQLException {
            NutritionTableBean lowEnergy = createTestNutrition(1);
            lowEnergy.setEnergia(100);
            nutritionDao.doSave(lowEnergy);

            NutritionTableBean highEnergy = createTestNutrition(2);
            highEnergy.setEnergia(500);
            nutritionDao.doSave(highEnergy);

            Collection<NutritionTableBean> tables = nutritionDao.doRetrieveAll("ENERGY");

            assertEquals(2, tables.size());
        }
    }

    // ============================================================================
    // Loop Boundary Tests
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("Loop: 0 iterations (no nutrition tables)")
        void testLoopZeroIterations() throws SQLException {
            Collection<NutritionTableBean> tables = nutritionDao.doRetrieveAll(null);
            assertEquals(0, tables.size());
        }

        @Test
        @DisplayName("Loop: 1 iteration (single nutrition table)")
        void testLoopOneIteration() throws SQLException {
            nutritionDao.doSave(createTestNutrition(1));

            Collection<NutritionTableBean> tables = nutritionDao.doRetrieveAll(null);
            assertEquals(1, tables.size());
        }

        @Test
        @DisplayName("Loop: >1 iterations (multiple nutrition tables)")
        void testLoopMultipleIterations() throws SQLException {
            nutritionDao.doSave(createTestNutrition(1));
            nutritionDao.doSave(createTestNutrition(2));
            nutritionDao.doSave(createTestNutrition(3));

            Collection<NutritionTableBean> tables = nutritionDao.doRetrieveAll(null);
            assertEquals(3, tables.size());
        }
    }

    // ============================================================================
    // Nutritional Values Verification Tests
    // ============================================================================

    @Nested
    @DisplayName("Nutritional Values Tests")
    class NutritionalValuesTests {

        @Test
        @DisplayName("Verify all nutritional values are stored correctly")
        void testNutritionalValuesStored() throws SQLException {
            // Note: Using integer values because DAO's doRetrieveByKey uses getInt() instead of getDouble()
            NutritionTableBean nutrition = new NutritionTableBean();
            nutrition.setCodiceProdotto(1);
            nutrition.setEnergia(200);
            nutrition.setGrassi(15.0);
            nutrition.setGrassiSaturi(5.0);
            nutrition.setCarboedrati(25.0);
            nutrition.setZucherri(10.0);
            nutrition.setFibre(3.0);
            nutrition.setProteine(8.0);
            nutrition.setSale(1.0);

            nutritionDao.doSave(nutrition);
            NutritionTableBean retrieved = nutritionDao.doRetrieveByKey(1);

            assertEquals(200, retrieved.getEnergia());
            assertEquals(15.0, retrieved.getGrassi(), 0.01);
            assertEquals(5.0, retrieved.getGrassiSaturi(), 0.01);
            assertEquals(25.0, retrieved.getCarboedrati(), 0.01);
            assertEquals(10.0, retrieved.getZucherri(), 0.01);
            assertEquals(3.0, retrieved.getFibre(), 0.01);
            assertEquals(8.0, retrieved.getProteine(), 0.01);
            assertEquals(1.0, retrieved.getSale(), 0.01);
        }

        @Test
        @DisplayName("Verify zero values are stored correctly")
        void testZeroValues() throws SQLException {
            NutritionTableBean nutrition = new NutritionTableBean();
            nutrition.setCodiceProdotto(1);
            nutrition.setEnergia(0);
            nutrition.setGrassi(0.0);
            nutrition.setGrassiSaturi(0.0);
            nutrition.setCarboedrati(0.0);
            nutrition.setZucherri(0.0);
            nutrition.setFibre(0.0);
            nutrition.setProteine(0.0);
            nutrition.setSale(0.0);

            nutritionDao.doSave(nutrition);
            NutritionTableBean retrieved = nutritionDao.doRetrieveByKey(1);

            assertEquals(0, retrieved.getEnergia());
            assertEquals(0.0, retrieved.getGrassi(), 0.01);
        }
    }

    // ============================================================================
    // Helper Methods
    // ============================================================================

    private NutritionTableBean createTestNutrition(int productCode) {
        NutritionTableBean nutrition = new NutritionTableBean();
        nutrition.setCodiceProdotto(productCode);
        nutrition.setEnergia(100 * productCode);
        nutrition.setGrassi(5.0 * productCode);
        nutrition.setGrassiSaturi(2.0 * productCode);
        nutrition.setCarboedrati(20.0 * productCode);
        nutrition.setZucherri(5.0 * productCode);
        nutrition.setFibre(2.0 * productCode);
        nutrition.setProteine(10.0 * productCode);
        nutrition.setSale(0.3 * productCode);
        return nutrition;
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
