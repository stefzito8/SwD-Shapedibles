package model.bean;

import categories.UnitTest;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for OrderBean.
 * 
 * Testing Level: Unit
 * Technique: Black-Box (Equivalence Class, Boundary Value) + Branch Coverage
 * 
 * ============================================================================
 * EQUIVALENCE CLASS DESIGN
 * ============================================================================
 * 
 * Field: codice (int)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-COD-1     | Default value              | 0                   | Yes    |
 * | EC-COD-2     | Valid positive             | 100                 | Yes    |
 * | EC-COD-3     | Large positive             | 999999              | Yes    |
 * -----------------------------------------------------------------
 * 
 * Field: saldo_totale (double)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-SAL-1     | Default value              | 0.0                 | Yes    |
 * | EC-SAL-2     | Valid positive             | 99.99               | Yes    |
 * | EC-SAL-3     | Negative                   | -10.0               | Yes*   |
 * | EC-SAL-4     | Large value                | 999999.99           | Yes    |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@UnitTest
@DisplayName("OrderBean Unit Tests")
public class OrderBeanTest {

    private OrderBean orderBean;

    @BeforeEach
    void setUp() {
        orderBean = new OrderBean();
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
            OrderBean bean = new OrderBean();
            assertNotNull(bean);
            assertEquals(" ", bean.getUtente());
            assertEquals(0, bean.getCodice());
            assertEquals(" ", bean.getIndirizzo());
            assertEquals(" ", bean.getStato());
            assertEquals(" ", bean.getDataOrdine());
            assertEquals(0.0, bean.getSaldoTotale(), 0.001);
        }
    }

    // ============================================================================
    // Utente Tests
    // ============================================================================

    @Nested
    @DisplayName("Utente Tests")
    class UtenteTests {

        @Test
        @DisplayName("Set and get valid utente")
        void testValidUtente() {
            orderBean.setUtente("customer1");
            assertEquals("customer1", orderBean.getUtente());
        }

        @Test
        @DisplayName("Set null utente")
        void testNullUtente() {
            orderBean.setUtente(null);
            assertNull(orderBean.getUtente());
        }

        @Test
        @DisplayName("Set empty utente")
        void testEmptyUtente() {
            orderBean.setUtente("");
            assertEquals("", orderBean.getUtente());
        }

        @Test
        @DisplayName("Verify default utente")
        void testDefaultUtente() {
            assertEquals(" ", orderBean.getUtente());
        }
    }

    // ============================================================================
    // Codice Tests
    // ============================================================================

    @Nested
    @DisplayName("Codice Tests")
    class CodiceTests {

        @Test
        @DisplayName("EC-COD-1: Verify default codice = 0")
        void testDefaultCodice() {
            assertEquals(0, orderBean.getCodice());
        }

        @Test
        @DisplayName("EC-COD-2: Set and get valid positive codice")
        void testValidCodice() {
            orderBean.setCodice(100);
            assertEquals(100, orderBean.getCodice());
        }

        @Test
        @DisplayName("EC-COD-3: Set large positive codice")
        void testLargeCodice() {
            orderBean.setCodice(999999);
            assertEquals(999999, orderBean.getCodice());
        }

        @Test
        @DisplayName("BV: codice = 1")
        void testOneCodice() {
            orderBean.setCodice(1);
            assertEquals(1, orderBean.getCodice());
        }

        @Test
        @DisplayName("BV: negative codice")
        void testNegativeCodice() {
            orderBean.setCodice(-1);
            assertEquals(-1, orderBean.getCodice());
        }

        @Test
        @DisplayName("BV: max integer codice")
        void testMaxCodice() {
            orderBean.setCodice(Integer.MAX_VALUE);
            assertEquals(Integer.MAX_VALUE, orderBean.getCodice());
        }
    }

    // ============================================================================
    // Indirizzo Tests
    // ============================================================================

    @Nested
    @DisplayName("Indirizzo Tests")
    class IndirizzoTests {

        @Test
        @DisplayName("Set and get valid indirizzo")
        void testValidIndirizzo() {
            orderBean.setIndirizzo("Via Roma 42, Rome");
            assertEquals("Via Roma 42, Rome", orderBean.getIndirizzo());
        }

        @Test
        @DisplayName("Set null indirizzo")
        void testNullIndirizzo() {
            orderBean.setIndirizzo(null);
            assertNull(orderBean.getIndirizzo());
        }

        @Test
        @DisplayName("Verify default indirizzo")
        void testDefaultIndirizzo() {
            assertEquals(" ", orderBean.getIndirizzo());
        }
    }

    // ============================================================================
    // Stato Tests
    // ============================================================================

    @Nested
    @DisplayName("Stato Tests")
    class StatoTests {

        @Test
        @DisplayName("Set and get stato = PENDING")
        void testPendingStato() {
            orderBean.setStato("PENDING");
            assertEquals("PENDING", orderBean.getStato());
        }

        @Test
        @DisplayName("Set and get stato = COMPLETED")
        void testCompletedStato() {
            orderBean.setStato("COMPLETED");
            assertEquals("COMPLETED", orderBean.getStato());
        }

        @Test
        @DisplayName("Set and get stato = SHIPPED")
        void testShippedStato() {
            orderBean.setStato("SHIPPED");
            assertEquals("SHIPPED", orderBean.getStato());
        }

        @Test
        @DisplayName("Set null stato")
        void testNullStato() {
            orderBean.setStato(null);
            assertNull(orderBean.getStato());
        }

        @Test
        @DisplayName("Verify default stato")
        void testDefaultStato() {
            assertEquals(" ", orderBean.getStato());
        }
    }

    // ============================================================================
    // DataOrdine Tests
    // ============================================================================

    @Nested
    @DisplayName("DataOrdine Tests")
    class DataOrdineTests {

        @Test
        @DisplayName("Set and get valid data_ordine")
        void testValidDataOrdine() {
            orderBean.setDataOrdine("2024-01-15");
            assertEquals("2024-01-15", orderBean.getDataOrdine());
        }

        @Test
        @DisplayName("Set null data_ordine")
        void testNullDataOrdine() {
            orderBean.setDataOrdine(null);
            assertNull(orderBean.getDataOrdine());
        }

        @Test
        @DisplayName("Verify default data_ordine")
        void testDefaultDataOrdine() {
            assertEquals(" ", orderBean.getDataOrdine());
        }
    }

    // ============================================================================
    // SaldoTotale Tests
    // ============================================================================

    @Nested
    @DisplayName("SaldoTotale Tests")
    class SaldoTotaleTests {

        @Test
        @DisplayName("EC-SAL-1: Verify default saldo_totale = 0.0")
        void testDefaultSaldoTotale() {
            assertEquals(0.0, orderBean.getSaldoTotale(), 0.001);
        }

        @Test
        @DisplayName("EC-SAL-2: Set and get valid positive saldo_totale")
        void testValidSaldoTotale() {
            orderBean.setSaldoTotale(99.99);
            assertEquals(99.99, orderBean.getSaldoTotale(), 0.001);
        }

        @Test
        @DisplayName("EC-SAL-3: Set negative saldo_totale")
        void testNegativeSaldoTotale() {
            orderBean.setSaldoTotale(-10.0);
            assertEquals(-10.0, orderBean.getSaldoTotale(), 0.001);
        }

        @Test
        @DisplayName("EC-SAL-4: Large saldo_totale value")
        void testLargeSaldoTotale() {
            orderBean.setSaldoTotale(999999.99);
            assertEquals(999999.99, orderBean.getSaldoTotale(), 0.001);
        }

        @Test
        @DisplayName("BV: saldo_totale = 0.01 (minimum positive)")
        void testMinPositiveSaldoTotale() {
            orderBean.setSaldoTotale(0.01);
            assertEquals(0.01, orderBean.getSaldoTotale(), 0.001);
        }

        @Test
        @DisplayName("BV: saldo_totale with many decimals")
        void testPrecisionSaldoTotale() {
            orderBean.setSaldoTotale(123.456789);
            assertEquals(123.456789, orderBean.getSaldoTotale(), 0.000001);
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
            orderBean.setUtente("customer1");
            orderBean.setCodice(100);
            orderBean.setIndirizzo("Via Roma");
            orderBean.setStato("PENDING");
            orderBean.setDataOrdine("2024-01-15");
            orderBean.setSaldoTotale(99.99);
            
            String result = orderBean.toString();
            assertTrue(result.contains("customer1"));
            assertTrue(result.contains("100"));
            assertTrue(result.contains("Via Roma"));
            assertTrue(result.contains("PENDING"));
            assertTrue(result.contains("2024-01-15"));
            assertTrue(result.contains("99.99"));
        }

        @Test
        @DisplayName("toString with default values")
        void testToStringDefaults() {
            String result = orderBean.toString();
            assertNotNull(result);
            assertTrue(result.contains("0"));
        }
    }
}
