package model.bean;

import categories.UnitTest;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for CouponBean.
 * 
 * Testing Level: Unit
 * Technique: Black-Box (Equivalence Class, Boundary Value) + Branch Coverage
 * 
 * ============================================================================
 * EQUIVALENCE CLASS DESIGN
 * ============================================================================
 * 
 * Field: codice (String)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-COD-1     | Valid coupon code          | "SAVE20"            | Yes    |
 * | EC-COD-2     | Empty string               | ""                  | Yes*   |
 * | EC-COD-3     | Null value                 | null                | Yes*   |
 * | EC-COD-4     | Default value              | " "                 | Yes    |
 * -----------------------------------------------------------------
 * 
 * Field: percentuale_sconto (int)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-PER-1     | Default value              | 0                   | Yes    |
 * | EC-PER-2     | Valid percentage           | 20                  | Yes    |
 * | EC-PER-3     | Maximum (100%)             | 100                 | Yes    |
 * | EC-PER-4     | Over 100%                  | 150                 | Yes*   |
 * | EC-PER-5     | Negative                   | -10                 | Yes*   |
 * -----------------------------------------------------------------
 * 
 * Field: saldo_minimo (double)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-MIN-1     | Default value              | 0.0                 | Yes    |
 * | EC-MIN-2     | Valid positive             | 50.0                | Yes    |
 * | EC-MIN-3     | Negative                   | -10.0               | Yes*   |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@UnitTest
@DisplayName("CouponBean Unit Tests")
public class CouponBeanTest {

    private CouponBean couponBean;

    @BeforeEach
    void setUp() {
        couponBean = new CouponBean();
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
            CouponBean bean = new CouponBean();
            assertNotNull(bean);
            assertEquals(" ", bean.getCodice());
            assertEquals(0, bean.getPercentualeSconto());
            assertEquals(0.0, bean.getSaldoMinimo(), 0.001);
        }
    }

    // ============================================================================
    // Codice Tests
    // ============================================================================

    @Nested
    @DisplayName("Codice Tests")
    class CodiceTests {

        @Test
        @DisplayName("EC-COD-1: Set and get valid coupon code")
        void testValidCode() {
            couponBean.setCodice("SAVE20");
            assertEquals("SAVE20", couponBean.getCodice());
        }

        @Test
        @DisplayName("EC-COD-2: Set empty code")
        void testEmptyCode() {
            couponBean.setCodice("");
            assertEquals("", couponBean.getCodice());
        }

        @Test
        @DisplayName("EC-COD-3: Set null code")
        void testNullCode() {
            couponBean.setCodice(null);
            assertNull(couponBean.getCodice());
        }

        @Test
        @DisplayName("EC-COD-4: Verify default code")
        void testDefaultCode() {
            assertEquals(" ", couponBean.getCodice());
        }

        @Test
        @DisplayName("BV: Long coupon code")
        void testLongCode() {
            String longCode = "SUPERSAVINGSSPECIALDEAL2024";
            couponBean.setCodice(longCode);
            assertEquals(longCode, couponBean.getCodice());
        }

        @Test
        @DisplayName("BV: Single character code")
        void testSingleCharCode() {
            couponBean.setCodice("A");
            assertEquals("A", couponBean.getCodice());
        }

        @Test
        @DisplayName("Code with special characters")
        void testSpecialCharCode() {
            couponBean.setCodice("SAVE-20%");
            assertEquals("SAVE-20%", couponBean.getCodice());
        }
    }

    // ============================================================================
    // PercentualeSconto Tests
    // ============================================================================

    @Nested
    @DisplayName("PercentualeSconto Tests")
    class PercentualeScontoTests {

        @Test
        @DisplayName("EC-PER-1: Verify default percentuale_sconto = 0")
        void testDefaultPercentualeSconto() {
            assertEquals(0, couponBean.getPercentualeSconto());
        }

        @Test
        @DisplayName("EC-PER-2: Set valid percentage (20%)")
        void testValidPercentage() {
            couponBean.setPercentualeSconto(20);
            assertEquals(20, couponBean.getPercentualeSconto());
        }

        @Test
        @DisplayName("EC-PER-3: Set maximum percentage (100%)")
        void testMaxPercentage() {
            couponBean.setPercentualeSconto(100);
            assertEquals(100, couponBean.getPercentualeSconto());
        }

        @Test
        @DisplayName("EC-PER-4: Set over 100%")
        void testOverMaxPercentage() {
            couponBean.setPercentualeSconto(150);
            assertEquals(150, couponBean.getPercentualeSconto());
        }

        @Test
        @DisplayName("EC-PER-5: Set negative percentage")
        void testNegativePercentage() {
            couponBean.setPercentualeSconto(-10);
            assertEquals(-10, couponBean.getPercentualeSconto());
        }

        @Test
        @DisplayName("BV: percentage = 1")
        void testOnePercentage() {
            couponBean.setPercentualeSconto(1);
            assertEquals(1, couponBean.getPercentualeSconto());
        }

        @Test
        @DisplayName("BV: percentage = 99")
        void test99Percentage() {
            couponBean.setPercentualeSconto(99);
            assertEquals(99, couponBean.getPercentualeSconto());
        }

        @Test
        @DisplayName("BV: percentage = 50 (midpoint)")
        void test50Percentage() {
            couponBean.setPercentualeSconto(50);
            assertEquals(50, couponBean.getPercentualeSconto());
        }
    }

    // ============================================================================
    // SaldoMinimo Tests
    // ============================================================================

    @Nested
    @DisplayName("SaldoMinimo Tests")
    class SaldoMinimoTests {

        @Test
        @DisplayName("EC-MIN-1: Verify default saldo_minimo = 0.0")
        void testDefaultSaldoMinimo() {
            assertEquals(0.0, couponBean.getSaldoMinimo(), 0.001);
        }

        @Test
        @DisplayName("EC-MIN-2: Set valid positive saldo_minimo")
        void testValidSaldoMinimo() {
            couponBean.setSaldoMinimo(50.0);
            assertEquals(50.0, couponBean.getSaldoMinimo(), 0.001);
        }

        @Test
        @DisplayName("EC-MIN-3: Set negative saldo_minimo")
        void testNegativeSaldoMinimo() {
            couponBean.setSaldoMinimo(-10.0);
            assertEquals(-10.0, couponBean.getSaldoMinimo(), 0.001);
        }

        @Test
        @DisplayName("BV: saldo_minimo = 0.01 (minimum positive)")
        void testMinPositiveSaldoMinimo() {
            couponBean.setSaldoMinimo(0.01);
            assertEquals(0.01, couponBean.getSaldoMinimo(), 0.001);
        }

        @Test
        @DisplayName("BV: large saldo_minimo")
        void testLargeSaldoMinimo() {
            couponBean.setSaldoMinimo(999999.99);
            assertEquals(999999.99, couponBean.getSaldoMinimo(), 0.001);
        }

        @Test
        @DisplayName("BV: saldo_minimo with precision")
        void testPrecisionSaldoMinimo() {
            couponBean.setSaldoMinimo(123.456);
            assertEquals(123.456, couponBean.getSaldoMinimo(), 0.001);
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
            couponBean.setCodice("SAVE20");
            couponBean.setPercentualeSconto(20);
            couponBean.setSaldoMinimo(50.0);
            
            String result = couponBean.toString();
            assertEquals("SAVE20 20 50.0", result);
        }

        @Test
        @DisplayName("toString with default values")
        void testToStringDefaults() {
            String result = couponBean.toString();
            assertEquals("  0 0.0", result);
        }

        @Test
        @DisplayName("toString with zero discount")
        void testToStringZeroDiscount() {
            couponBean.setCodice("FREE");
            couponBean.setPercentualeSconto(0);
            couponBean.setSaldoMinimo(0.0);
            
            String result = couponBean.toString();
            assertEquals("FREE 0 0.0", result);
        }

        @Test
        @DisplayName("toString with 100% discount")
        void testToStringFullDiscount() {
            couponBean.setCodice("FREE100");
            couponBean.setPercentualeSconto(100);
            couponBean.setSaldoMinimo(100.0);
            
            String result = couponBean.toString();
            assertEquals("FREE100 100 100.0", result);
        }
    }
}
