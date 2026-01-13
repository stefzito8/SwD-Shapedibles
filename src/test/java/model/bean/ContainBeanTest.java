package model.bean;

import categories.UnitTest;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for ContainBean.
 * 
 * Testing Level: Unit
 * Technique: Black-Box (Equivalence Class, Boundary Value) + Branch Coverage
 * 
 * ============================================================================
 * EQUIVALENCE CLASS DESIGN
 * ============================================================================
 * 
 * Field: codice_ordine (int)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-ORD-1     | Default value              | -1                  | Yes    |
 * | EC-ORD-2     | Valid positive             | 100                 | Yes    |
 * | EC-ORD-3     | Zero                       | 0                   | Yes    |
 * -----------------------------------------------------------------
 * 
 * Field: quantità (int)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-QTY-1     | Default value              | 1                   | Yes    |
 * | EC-QTY-2     | Valid positive             | 5                   | Yes    |
 * | EC-QTY-3     | Zero                       | 0                   | Yes*   |
 * | EC-QTY-4     | Large value                | 9999                | Yes    |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@UnitTest
@DisplayName("ContainBean Unit Tests")
public class ContainBeanTest {

    private ContainBean containBean;

    @BeforeEach
    void setUp() {
        containBean = new ContainBean();
    }

    // ============================================================================
    // Constructor Tests
    // ============================================================================

    @Nested
    @DisplayName("Constructor Tests")
    class ConstructorTests {

        @Test
        @DisplayName("Default constructor initializes with default values")
        void testDefaultConstructor() {
            ContainBean bean = new ContainBean();
            assertNotNull(bean);
            assertEquals(-1, bean.getCodiceOrdine());
            assertEquals(-1, bean.getCodiceProdotto());
            assertEquals(1, bean.getQuantità());
        }
    }

    // ============================================================================
    // CodiceOrdine Tests
    // ============================================================================

    @Nested
    @DisplayName("CodiceOrdine Tests")
    class CodiceOrdineTests {

        @Test
        @DisplayName("EC-ORD-1: Verify default codice_ordine = -1")
        void testDefaultCodiceOrdine() {
            assertEquals(-1, containBean.getCodiceOrdine());
        }

        @Test
        @DisplayName("EC-ORD-2: Set and get valid positive codice_ordine")
        void testValidCodiceOrdine() {
            containBean.setCodiceOrdine(100);
            assertEquals(100, containBean.getCodiceOrdine());
        }

        @Test
        @DisplayName("EC-ORD-3: Set codice_ordine = 0")
        void testZeroCodiceOrdine() {
            containBean.setCodiceOrdine(0);
            assertEquals(0, containBean.getCodiceOrdine());
        }

        @Test
        @DisplayName("BV: codice_ordine = 1")
        void testOneCodiceOrdine() {
            containBean.setCodiceOrdine(1);
            assertEquals(1, containBean.getCodiceOrdine());
        }

        @Test
        @DisplayName("BV: large codice_ordine")
        void testLargeCodiceOrdine() {
            containBean.setCodiceOrdine(999999);
            assertEquals(999999, containBean.getCodiceOrdine());
        }
    }

    // ============================================================================
    // CodiceProdotto Tests
    // ============================================================================

    @Nested
    @DisplayName("CodiceProdotto Tests")
    class CodiceProdottoTests {

        @Test
        @DisplayName("Verify default codice_prodotto = -1")
        void testDefaultCodiceProdotto() {
            assertEquals(-1, containBean.getCodiceProdotto());
        }

        @Test
        @DisplayName("Set and get valid positive codice_prodotto")
        void testValidCodiceProdotto() {
            containBean.setCodiceProdotto(200);
            assertEquals(200, containBean.getCodiceProdotto());
        }

        @Test
        @DisplayName("Set codice_prodotto = 0")
        void testZeroCodiceProdotto() {
            containBean.setCodiceProdotto(0);
            assertEquals(0, containBean.getCodiceProdotto());
        }

        @Test
        @DisplayName("BV: codice_prodotto = 1")
        void testOneCodiceProdotto() {
            containBean.setCodiceProdotto(1);
            assertEquals(1, containBean.getCodiceProdotto());
        }

        @Test
        @DisplayName("BV: large codice_prodotto")
        void testLargeCodiceProdotto() {
            containBean.setCodiceProdotto(999999);
            assertEquals(999999, containBean.getCodiceProdotto());
        }
    }

    // ============================================================================
    // Quantità Tests
    // ============================================================================

    @Nested
    @DisplayName("Quantità Tests")
    class QuantitàTests {

        @Test
        @DisplayName("EC-QTY-1: Verify default quantità = 1")
        void testDefaultQuantità() {
            assertEquals(1, containBean.getQuantità());
        }

        @Test
        @DisplayName("EC-QTY-2: Set and get valid positive quantità")
        void testValidQuantità() {
            containBean.setQuantità(5);
            assertEquals(5, containBean.getQuantità());
        }

        @Test
        @DisplayName("EC-QTY-3: Set quantità = 0")
        void testZeroQuantità() {
            containBean.setQuantità(0);
            assertEquals(0, containBean.getQuantità());
        }

        @Test
        @DisplayName("EC-QTY-4: Set large quantità")
        void testLargeQuantità() {
            containBean.setQuantità(9999);
            assertEquals(9999, containBean.getQuantità());
        }

        @Test
        @DisplayName("BV: quantità = 1 (boundary)")
        void testOneQuantità() {
            containBean.setQuantità(1);
            assertEquals(1, containBean.getQuantità());
        }

        @Test
        @DisplayName("BV: quantità = 2")
        void testTwoQuantità() {
            containBean.setQuantità(2);
            assertEquals(2, containBean.getQuantità());
        }

        @Test
        @DisplayName("BV: negative quantità")
        void testNegativeQuantità() {
            containBean.setQuantità(-1);
            assertEquals(-1, containBean.getQuantità());
        }
    }

    // ============================================================================
    // ToString Tests
    // ============================================================================

    @Nested
    @DisplayName("ToString Tests")
    class ToStringTests {

        @Test
        @DisplayName("toString returns all fields formatted")
        void testToString() {
            containBean.setCodiceOrdine(100);
            containBean.setCodiceProdotto(200);
            containBean.setQuantità(5);
            
            String result = containBean.toString();
            assertEquals("100 200 5", result);
        }

        @Test
        @DisplayName("toString with default values")
        void testToStringDefaults() {
            String result = containBean.toString();
            assertEquals("-1 -1 1", result);
        }

        @Test
        @DisplayName("toString with zero values")
        void testToStringZeros() {
            containBean.setCodiceOrdine(0);
            containBean.setCodiceProdotto(0);
            containBean.setQuantità(0);
            
            String result = containBean.toString();
            assertEquals("0 0 0", result);
        }
    }
}
