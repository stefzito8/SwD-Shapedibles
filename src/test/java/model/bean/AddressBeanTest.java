package model.bean;

import categories.UnitTest;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for AddressBean.
 * 
 * Testing Level: Unit
 * Technique: Black-Box (Equivalence Class, Boundary Value) + Branch Coverage
 * 
 * ============================================================================
 * EQUIVALENCE CLASS DESIGN
 * ============================================================================
 * 
 * Field: id (String)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-ID-1      | Valid non-empty string     | "1"                 | Yes    |
 * | EC-ID-2      | Empty string               | ""                  | Yes*   |
 * | EC-ID-3      | Null value                 | null                | Yes*   |
 * -----------------------------------------------------------------
 * 
 * Field: numero (int)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-NUM-1     | Valid positive             | 42                  | Yes    |
 * | EC-NUM-2     | Zero                       | 0                   | Yes    |
 * | EC-NUM-3     | Negative                   | -1                  | Yes*   |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@UnitTest
@DisplayName("AddressBean Unit Tests")
public class AddressBeanTest {

    private AddressBean addressBean;

    @BeforeEach
    void setUp() {
        addressBean = new AddressBean();
    }

    // ============================================================================
    // ID Tests
    // ============================================================================

    @Nested
    @DisplayName("ID Tests")
    class IdTests {

        @Test
        @DisplayName("EC-ID-1: Set and get valid ID")
        void testValidId() {
            addressBean.setId("1");
            assertEquals("1", addressBean.getId());
        }

        @Test
        @DisplayName("EC-ID-2: Set empty ID")
        void testEmptyId() {
            addressBean.setId("");
            assertEquals("", addressBean.getId());
        }

        @Test
        @DisplayName("EC-ID-3: Set null ID")
        void testNullId() {
            addressBean.setId(null);
            assertNull(addressBean.getId());
        }

        @Test
        @DisplayName("BV: Long ID string")
        void testLongId() {
            String longId = "12345678901234567890";
            addressBean.setId(longId);
            assertEquals(longId, addressBean.getId());
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
            addressBean.setUtente("testuser");
            assertEquals("testuser", addressBean.getUtente());
        }

        @Test
        @DisplayName("Set null utente")
        void testNullUtente() {
            addressBean.setUtente(null);
            assertNull(addressBean.getUtente());
        }

        @Test
        @DisplayName("Set empty utente")
        void testEmptyUtente() {
            addressBean.setUtente("");
            assertEquals("", addressBean.getUtente());
        }
    }

    // ============================================================================
    // Paese Tests
    // ============================================================================

    @Nested
    @DisplayName("Paese Tests")
    class PaeseTests {

        @Test
        @DisplayName("Set and get valid paese")
        void testValidPaese() {
            addressBean.setPaese("Italy");
            assertEquals("Italy", addressBean.getPaese());
        }

        @Test
        @DisplayName("Set null paese")
        void testNullPaese() {
            addressBean.setPaese(null);
            assertNull(addressBean.getPaese());
        }

        @Test
        @DisplayName("Set empty paese")
        void testEmptyPaese() {
            addressBean.setPaese("");
            assertEquals("", addressBean.getPaese());
        }
    }

    // ============================================================================
    // Strada Tests
    // ============================================================================

    @Nested
    @DisplayName("Strada Tests")
    class StradaTests {

        @Test
        @DisplayName("Set and get valid strada")
        void testValidStrada() {
            addressBean.setStrada("Via Roma");
            assertEquals("Via Roma", addressBean.getStrada());
        }

        @Test
        @DisplayName("Set null strada")
        void testNullStrada() {
            addressBean.setStrada(null);
            assertNull(addressBean.getStrada());
        }

        @Test
        @DisplayName("Set empty strada")
        void testEmptyStrada() {
            addressBean.setStrada("");
            assertEquals("", addressBean.getStrada());
        }
    }

    // ============================================================================
    // Città Tests
    // ============================================================================

    @Nested
    @DisplayName("Città Tests")
    class CittàTests {

        @Test
        @DisplayName("Set and get valid città")
        void testValidCittà() {
            addressBean.setCittà("Rome");
            assertEquals("Rome", addressBean.getCittà());
        }

        @Test
        @DisplayName("Set null città")
        void testNullCittà() {
            addressBean.setCittà(null);
            assertNull(addressBean.getCittà());
        }

        @Test
        @DisplayName("Set empty città")
        void testEmptyCittà() {
            addressBean.setCittà("");
            assertEquals("", addressBean.getCittà());
        }
    }

    // ============================================================================
    // Numero Tests
    // ============================================================================

    @Nested
    @DisplayName("Numero Tests")
    class NumeroTests {

        @Test
        @DisplayName("EC-NUM-1: Set and get valid positive numero")
        void testValidNumero() {
            addressBean.setNumero(42);
            assertEquals(42, addressBean.getNumero());
        }

        @Test
        @DisplayName("EC-NUM-2: Set numero = 0")
        void testZeroNumero() {
            addressBean.setNumero(0);
            assertEquals(0, addressBean.getNumero());
        }

        @Test
        @DisplayName("EC-NUM-3: Set negative numero")
        void testNegativeNumero() {
            addressBean.setNumero(-1);
            assertEquals(-1, addressBean.getNumero());
        }

        @Test
        @DisplayName("BV: Set numero = 1")
        void testOneNumero() {
            addressBean.setNumero(1);
            assertEquals(1, addressBean.getNumero());
        }

        @Test
        @DisplayName("BV: Large numero")
        void testLargeNumero() {
            addressBean.setNumero(99999);
            assertEquals(99999, addressBean.getNumero());
        }
    }

    // ============================================================================
    // CodicePostale Tests
    // ============================================================================

    @Nested
    @DisplayName("CodicePostale Tests")
    class CodicePostaleTests {

        @Test
        @DisplayName("Set and get valid codice_postale")
        void testValidCodicePostale() {
            addressBean.setCodicePostale("00100");
            assertEquals("00100", addressBean.getCodicePostale());
        }

        @Test
        @DisplayName("Set null codice_postale")
        void testNullCodicePostale() {
            addressBean.setCodicePostale(null);
            assertNull(addressBean.getCodicePostale());
        }

        @Test
        @DisplayName("Set empty codice_postale")
        void testEmptyCodicePostale() {
            addressBean.setCodicePostale("");
            assertEquals("", addressBean.getCodicePostale());
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
            addressBean.setId("1");
            addressBean.setUtente("user1");
            addressBean.setPaese("Italy");
            addressBean.setStrada("Via Roma");
            addressBean.setCittà("Rome");
            addressBean.setNumero(42);
            addressBean.setCodicePostale("00100");
            
            String result = addressBean.toString();
            assertTrue(result.contains("1"));
            assertTrue(result.contains("user1"));
            assertTrue(result.contains("Italy"));
            assertTrue(result.contains("Via Roma"));
            assertTrue(result.contains("Rome"));
            assertTrue(result.contains("42"));
            assertTrue(result.contains("00100"));
        }

        @Test
        @DisplayName("toString with null fields")
        void testToStringWithNulls() {
            // Should not throw exception even with null fields
            assertDoesNotThrow(() -> addressBean.toString());
        }
    }

    // ============================================================================
    // SelectString Tests
    // ============================================================================

    @Nested
    @DisplayName("SelectString Tests")
    class SelectStringTests {

        @Test
        @DisplayName("selectString returns formatted address")
        void testSelectString() {
            addressBean.setPaese("Italy");
            addressBean.setStrada("Via Roma");
            addressBean.setCittà("Rome");
            addressBean.setNumero(42);
            addressBean.setCodicePostale("00100");
            
            String result = addressBean.selectString();
            assertEquals("Italy, Via Roma, Rome, 42, 00100", result);
        }

        @Test
        @DisplayName("selectString with minimal data")
        void testSelectStringMinimal() {
            addressBean.setPaese("USA");
            addressBean.setStrada("Main St");
            addressBean.setCittà("NYC");
            addressBean.setNumero(1);
            addressBean.setCodicePostale("10001");
            
            String result = addressBean.selectString();
            assertTrue(result.contains("USA"));
            assertTrue(result.contains("Main St"));
        }
    }
}
