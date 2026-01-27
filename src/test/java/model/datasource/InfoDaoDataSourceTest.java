package model.datasource;

import categories.IntegrationTest;
import integration.H2TestDatabase;
import model.bean.InfoBean;
import org.junit.jupiter.api.*;

import javax.sql.DataSource;
import java.sql.SQLException;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Integration tests for InfoDaoDataSource.
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
 * | INFO-B1   | rs.next() (while)            | Populate bean     | Return default |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveByName(String name)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | INFO-B2   | rs.next() (while)            | Populate bean     | Return default |
 * -----------------------------------------------------------------
 * 
 * Method: doDelete(int code)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | INFO-B3   | result != 0                  | Return true       | Return false   |
 * -----------------------------------------------------------------
 * 
 * Method: doRetrieveAll(String order)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | INFO-B4   | order != null && !order.equals("") | Add ORDER BY | No ORDER BY  |
 * | INFO-B5   | rs.next() (while loop)       | Add to collection | Exit loop     |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@IntegrationTest
@DisplayName("InfoDaoDataSource Integration Tests")
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
public class InfoDaoDataSourceTest {

    private static DataSource dataSource;
    private InfoDaoDataSource infoDao;

    @BeforeAll
    static void setUpClass() {
        dataSource = H2TestDatabase.getDataSource();
        H2TestDatabase.initializeDatabase();
    }

    @BeforeEach
    void setUp() {
        H2TestDatabase.resetDatabase();
        infoDao = new InfoDaoDataSource(dataSource);
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
        @DisplayName("Save new info successfully")
        void testSaveNewInfo() throws SQLException {
            InfoBean info = createTestInfo("Test Product", 9.99, "Description", 100, "Type1");

            infoDao.doSave(info);

            Collection<InfoBean> infos = infoDao.doRetrieveAll(null);
            assertEquals(1, infos.size());
        }

        @Test
        @DisplayName("Save info with all fields")
        void testSaveInfoAllFields() throws SQLException {
            InfoBean info = createTestInfo("Full Product", 25.50, "Full description", 50, "Category");

            infoDao.doSave(info);

            InfoBean retrieved = infoDao.doRetrieveByName("Full Product");
            assertEquals("Full Product", retrieved.getNome());
            assertEquals(25.50, retrieved.getCosto(), 0.01);
            assertEquals("Full description", retrieved.getDescrizione());
            assertEquals(50, retrieved.getDisponibilità());
            assertEquals("Category", retrieved.getTipologia());
        }

        @Test
        @DisplayName("Save multiple infos")
        void testSaveMultipleInfos() throws SQLException {
            infoDao.doSave(createTestInfo("Info 1", 10.0, "Desc 1", 10, "Type1"));
            infoDao.doSave(createTestInfo("Info 2", 20.0, "Desc 2", 20, "Type2"));
            infoDao.doSave(createTestInfo("Info 3", 30.0, "Desc 3", 30, "Type3"));

            Collection<InfoBean> infos = infoDao.doRetrieveAll(null);
            assertEquals(3, infos.size());
        }
    }

    // ============================================================================
    // doRetrieveByKey Tests (Branch INFO-B1)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByKey Tests")
    class DoRetrieveByKeyTests {

        @Test
        @DisplayName("B1-True: Retrieve existing info by code")
        void testRetrieveExistingByKey() throws SQLException {
            infoDao.doSave(createTestInfo("Test Info", 15.0, "Test", 25, "TestType"));
            Collection<InfoBean> all = infoDao.doRetrieveAll(null);
            int code = all.iterator().next().getCodice();

            InfoBean retrieved = infoDao.doRetrieveByKey(code);

            assertNotNull(retrieved);
            assertEquals("Test Info", retrieved.getNome());
        }

        @Test
        @DisplayName("B1-False: Retrieve non-existent info returns default bean")
        void testRetrieveNonExistentByKey() throws SQLException {
            InfoBean retrieved = infoDao.doRetrieveByKey(999);

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodice());
        }

        @Test
        @DisplayName("Retrieve with code = 0")
        void testRetrieveZeroCode() throws SQLException {
            InfoBean retrieved = infoDao.doRetrieveByKey(0);

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodice());
        }
    }

    // ============================================================================
    // doRetrieveByName Tests (Branch INFO-B2)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveByName Tests")
    class DoRetrieveByNameTests {

        @Test
        @DisplayName("B2-True: Retrieve existing info by name")
        void testRetrieveExistingByName() throws SQLException {
            infoDao.doSave(createTestInfo("Unique Name", 12.0, "Desc", 10, "Type"));

            InfoBean retrieved = infoDao.doRetrieveByName("Unique Name");

            assertNotNull(retrieved);
            assertEquals("Unique Name", retrieved.getNome());
        }

        @Test
        @DisplayName("B2-False: Retrieve non-existent info by name returns default")
        void testRetrieveNonExistentByName() throws SQLException {
            InfoBean retrieved = infoDao.doRetrieveByName("NonExistent");

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodice());
        }

        @Test
        @DisplayName("Verify all fields are set in doRetrieveByName")
        void testRetrieveByNameVerifiesAllFields() throws SQLException {
            infoDao.doSave(createTestInfo("Complete Product", 42.50, "Detailed desc", 75, "Premium"));

            InfoBean retrieved = infoDao.doRetrieveByName("Complete Product");

            // Verify all setters were called - kills mutations on setCodice, setNome, setCosto, setDescrizione, setDisponibilità, setTipologia
            assertTrue(retrieved.getCodice() > 0, "Codice should be set");
            assertEquals("Complete Product", retrieved.getNome(), "Nome should be set correctly");
            assertEquals(42.50, retrieved.getCosto(), 0.01, "Costo should be set correctly");
            assertEquals("Detailed desc", retrieved.getDescrizione(), "Descrizione should be set correctly");
            assertEquals(75, retrieved.getDisponibilità(), "Disponibilità should be set correctly");
            assertEquals("Premium", retrieved.getTipologia(), "Tipologia should be set correctly");
        }

        @Test
        @DisplayName("Retrieve with empty name")
        void testRetrieveEmptyName() throws SQLException {
            InfoBean retrieved = infoDao.doRetrieveByName("");

            assertNotNull(retrieved);
            assertEquals(-1, retrieved.getCodice());
        }
    }

    // ============================================================================
    // doDelete Tests (Branch INFO-B3)
    // ============================================================================

    @Nested
    @DisplayName("doDelete Tests")
    class DoDeleteTests {

        @Test
        @DisplayName("B3-True: Delete existing info returns true")
        void testDeleteExistingInfo() throws SQLException {
            infoDao.doSave(createTestInfo("To Delete", 5.0, "Delete me", 1, "Type"));
            Collection<InfoBean> all = infoDao.doRetrieveAll(null);
            int code = all.iterator().next().getCodice();

            boolean result = infoDao.doDelete(code);

            assertTrue(result);
            InfoBean retrieved = infoDao.doRetrieveByKey(code);
            assertEquals(-1, retrieved.getCodice());
        }

        @Test
        @DisplayName("B3-False: Delete non-existent info returns false")
        void testDeleteNonExistentInfo() throws SQLException {
            boolean result = infoDao.doDelete(999);

            assertFalse(result);
        }

        @Test
        @DisplayName("Delete with code = 0")
        void testDeleteZeroCode() throws SQLException {
            boolean result = infoDao.doDelete(0);

            assertFalse(result);
        }
    }

    // ============================================================================
    // doRetrieveAll Tests (Branches INFO-B4, INFO-B5)
    // ============================================================================

    @Nested
    @DisplayName("doRetrieveAll Tests")
    class DoRetrieveAllTests {

        @Test
        @DisplayName("B4-False, B5-False: Retrieve all from empty table")
        void testRetrieveAllEmpty() throws SQLException {
            Collection<InfoBean> infos = infoDao.doRetrieveAll(null);

            assertNotNull(infos);
            assertTrue(infos.isEmpty());
        }

        @Test
        @DisplayName("B4-False, B5-True: Retrieve all without order")
        void testRetrieveAllWithoutOrder() throws SQLException {
            infoDao.doSave(createTestInfo("Info A", 10.0, "Desc A", 10, "TypeA"));
            infoDao.doSave(createTestInfo("Info B", 20.0, "Desc B", 20, "TypeB"));

            Collection<InfoBean> infos = infoDao.doRetrieveAll(null);

            assertEquals(2, infos.size());
        }

        @Test
        @DisplayName("B4-True, B5-True: Retrieve all with order by name")
        void testRetrieveAllWithOrder() throws SQLException {
            infoDao.doSave(createTestInfo("B Info", 10.0, "Desc", 10, "Type"));
            infoDao.doSave(createTestInfo("A Info", 20.0, "Desc", 20, "Type"));

            Collection<InfoBean> infos = infoDao.doRetrieveAll("NAME");

            assertEquals(2, infos.size());
            InfoBean first = infos.iterator().next();
            assertEquals("A Info", first.getNome());
        }

        @Test
        @DisplayName("Verify all fields are populated in doRetrieveAll")
        void testRetrieveAllVerifiesAllFields() throws SQLException {
            infoDao.doSave(createTestInfo("Complete Info", 55.99, "Full Description", 150, "SpecialType"));

            Collection<InfoBean> infos = infoDao.doRetrieveAll(null);

            assertEquals(1, infos.size());
            InfoBean retrieved = infos.iterator().next();
            
            // Verify all setters were called - kills mutations on setCodice, setNome, setCosto, setDescrizione, setDisponibilità, setTipologia
            assertTrue(retrieved.getCodice() > 0, "Codice should be set");
            assertEquals("Complete Info", retrieved.getNome(), "Nome should be set correctly");
            assertEquals(55.99, retrieved.getCosto(), 0.01, "Costo should be set correctly");
            assertEquals("Full Description", retrieved.getDescrizione(), "Descrizione should be set correctly");
            assertEquals(150, retrieved.getDisponibilità(), "Disponibilità should be set correctly");
            assertEquals("SpecialType", retrieved.getTipologia(), "Tipologia should be set correctly");
        }

        @Test
        @DisplayName("B4-False: Retrieve all with empty order string")
        void testRetrieveAllEmptyOrder() throws SQLException {
            infoDao.doSave(createTestInfo("Test", 10.0, "Desc", 10, "Type"));

            Collection<InfoBean> infos = infoDao.doRetrieveAll("");

            assertEquals(1, infos.size());
        }

        @Test
        @DisplayName("Retrieve all with order by price")
        void testRetrieveAllOrderByPrice() throws SQLException {
            infoDao.doSave(createTestInfo("Expensive", 100.0, "Desc", 10, "Type"));
            infoDao.doSave(createTestInfo("Cheap", 5.0, "Desc", 10, "Type"));

            Collection<InfoBean> infos = infoDao.doRetrieveAll("PRICE");

            assertEquals(2, infos.size());
        }
    }

    // ============================================================================
    // doUpdateQuantity Tests
    // ============================================================================

    @Nested
    @DisplayName("doUpdateQuantity Tests")
    class DoUpdateQuantityTests {

        @Test
        @DisplayName("Update quantity of existing product")
        void testUpdateQuantityExisting() throws SQLException {
            // Save a product first
            infoDao.doSave(createTestInfo("Test Product", 9.99, "Description", 100, "Type1"));
            Collection<InfoBean> all = infoDao.doRetrieveAll(null);
            int code = all.iterator().next().getCodice();

            // Update the quantity
            infoDao.doUpdateQuantity(code, 50);

            // Verify the update
            InfoBean retrieved = infoDao.doRetrieveByKey(code);
            assertEquals(50, retrieved.getDisponibilità());
        }

        @Test
        @DisplayName("Update quantity to zero")
        void testUpdateQuantityToZero() throws SQLException {
            infoDao.doSave(createTestInfo("Zero Qty", 5.0, "Desc", 25, "Type"));
            Collection<InfoBean> all = infoDao.doRetrieveAll(null);
            int code = all.iterator().next().getCodice();

            infoDao.doUpdateQuantity(code, 0);

            InfoBean retrieved = infoDao.doRetrieveByKey(code);
            assertEquals(0, retrieved.getDisponibilità());
        }

        @Test
        @DisplayName("Update quantity of non-existent product does not throw")
        void testUpdateQuantityNonExistent() throws SQLException {
            // Should not throw even for non-existent product
            assertDoesNotThrow(() -> infoDao.doUpdateQuantity(999, 100));
        }

        @Test
        @DisplayName("Update quantity multiple times")
        void testUpdateQuantityMultipleTimes() throws SQLException {
            infoDao.doSave(createTestInfo("Multi Update", 10.0, "Desc", 100, "Type"));
            Collection<InfoBean> all = infoDao.doRetrieveAll(null);
            int code = all.iterator().next().getCodice();

            infoDao.doUpdateQuantity(code, 75);
            infoDao.doUpdateQuantity(code, 50);
            infoDao.doUpdateQuantity(code, 25);

            InfoBean retrieved = infoDao.doRetrieveByKey(code);
            assertEquals(25, retrieved.getDisponibilità());
        }
    }

    // ============================================================================
    // Loop Boundary Tests
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("Loop: 0 iterations (no infos)")
        void testLoopZeroIterations() throws SQLException {
            Collection<InfoBean> infos = infoDao.doRetrieveAll(null);
            assertEquals(0, infos.size());
        }

        @Test
        @DisplayName("Loop: 1 iteration (single info)")
        void testLoopOneIteration() throws SQLException {
            infoDao.doSave(createTestInfo("Single", 10.0, "Desc", 10, "Type"));

            Collection<InfoBean> infos = infoDao.doRetrieveAll(null);
            assertEquals(1, infos.size());
        }

        @Test
        @DisplayName("Loop: >1 iterations (multiple infos)")
        void testLoopMultipleIterations() throws SQLException {
            for (int i = 1; i <= 10; i++) {
                infoDao.doSave(createTestInfo("Info " + i, i * 5.0, "Desc " + i, i * 10, "Type" + i));
            }

            Collection<InfoBean> infos = infoDao.doRetrieveAll(null);
            assertEquals(10, infos.size());
        }
    }

    // ============================================================================
    // Mutation Killer Tests
    // ============================================================================

    @Nested
    @DisplayName("Mutation Killer Tests")
    class MutationKillerTests {
        
        @Test
        @DisplayName("doSave actually persists data - kills VoidMethodCallMutator line 46")
        void testDoSaveActuallyPersists() throws SQLException {
            InfoBean info = createTestInfo("MutInfo", 29.99, "Mutation test", 100, "TestType");
            
            // Verify empty before save
            Collection<InfoBean> beforeSave = infoDao.doRetrieveAll(null);
            assertEquals(0, beforeSave.size(), "Should be empty before save");
            
            // Save the info
            infoDao.doSave(info);
            
            // Verify present after save
            Collection<InfoBean> afterSave = infoDao.doRetrieveAll(null);
            assertEquals(1, afterSave.size(), "Should have 1 info after save");
            
            // Verify correct data was saved
            InfoBean saved = afterSave.iterator().next();
            assertEquals("MutInfo", saved.getNome());
            assertEquals(29.99, saved.getCosto(), 0.01);
            assertEquals("Mutation test", saved.getDescrizione());
        }
        
        @Test
        @DisplayName("doRetrieveByName returns correct info - kills NegateConditionalsMutator line 151")
        void testDoRetrieveByNameReturnsCorrectInfo() throws SQLException {
            infoDao.doSave(createTestInfo("NamedInfo", 49.99, "Named test", 50, "NameType"));
            
            InfoBean result = infoDao.doRetrieveByName("NamedInfo");
            
            assertNotNull(result);
            assertEquals("NamedInfo", result.getNome());
            assertEquals(49.99, result.getCosto(), 0.01);
            assertEquals("Named test", result.getDescrizione());
            assertEquals(50, result.getDisponibilità());
            assertEquals("NameType", result.getTipologia());
        }
        
        @Test
        @DisplayName("doRetrieveAll returns correct collection - kills EmptyObjectReturnValsMutator line 193")
        void testDoRetrieveAllReturnsCorrectCollection() throws SQLException {
            infoDao.doSave(createTestInfo("Info1", 10.0, "Desc1", 10, "Type1"));
            infoDao.doSave(createTestInfo("Info2", 20.0, "Desc2", 20, "Type2"));
            infoDao.doSave(createTestInfo("Info3", 30.0, "Desc3", 30, "Type3"));
            
            Collection<InfoBean> result = infoDao.doRetrieveAll(null);
            
            // Must use the returned collection
            assertNotNull(result, "Result must not be null");
            assertFalse(result.isEmpty(), "Result must not be empty");
            assertEquals(3, result.size(), "Must have 3 infos");
        }
        
        @Test
        @DisplayName("doUpdateQuantity actually updates - kills VoidMethodCallMutator line 221")
        void testDoUpdateQuantityActuallyUpdates() throws SQLException {
            infoDao.doSave(createTestInfo("QuantityInfo", 15.0, "Quantity test", 100, "QType"));
            
            // Get the saved info
            InfoBean savedInfo = infoDao.doRetrieveByName("QuantityInfo");
            int originalQuantity = savedInfo.getDisponibilità();
            assertEquals(100, originalQuantity);
            
            // Update quantity
            infoDao.doUpdateQuantity(savedInfo.getCodice(), 50);
            
            // Verify the update took effect
            InfoBean updated = infoDao.doRetrieveByName("QuantityInfo");
            assertEquals(50, updated.getDisponibilità());
            assertNotEquals(originalQuantity, updated.getDisponibilità());
        }
    }

    // ============================================================================
    // Helper Methods
    // ============================================================================

    private InfoBean createTestInfo(String nome, double costo, String descrizione, int disponibilita, String tipologia) {
        InfoBean info = new InfoBean();
        info.setNome(nome);
        info.setCosto(costo);
        info.setDescrizione(descrizione);
        info.setDisponibilità(disponibilita);
        info.setTipologia(tipologia);
        return info;
    }
}
