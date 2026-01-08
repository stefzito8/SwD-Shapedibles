package model.bean;

import categories.UnitTest;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for InfoBean.
 * 
 * Testing Level: Unit
 * Technique: Black-Box (Equivalence Class Testing, Boundary Value Testing)
 * 
 * ============================================================================
 * EQUIVALENCE CLASS DESIGN (Step 2.1)
 * ============================================================================
 * 
 * Field: descrizione (description)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value      | Valid? |
 * |--------------|-----------------------------|--------------------------|--------|
 * | EC-DESC-1    | Valid non-empty string     | "Delicious protein bar"  | Yes    |
 * | EC-DESC-2    | Empty string               | ""                       | Yes*   |
 * | EC-DESC-3    | Null value                 | null                     | Yes*   |
 * | EC-DESC-4    | Max length string (100)    | "A".repeat(100)          | Yes    |
 * | EC-DESC-5    | Over max length (101+)     | "A".repeat(101)          | No     |
 * | EC-DESC-6    | Description with newlines  | "Line1\nLine2"           | Yes    |
 * -----------------------------------------------------------------
 * 
 * Field: costo (cost/price)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-COST-1    | Valid positive price       | 9.99                | Yes    |
 * | EC-COST-2    | Zero price                 | 0.0                 | Yes    |
 * | EC-COST-3    | Negative price             | -1.0                | No     |
 * | EC-COST-4    | Very small positive        | 0.01                | Yes    |
 * | EC-COST-5    | Large price                | 9999.99             | Yes    |
 * | EC-COST-6    | Price with many decimals   | 9.999               | Yes    |
 * -----------------------------------------------------------------
 * 
 * Field: disponibilità (availability/quantity)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-DISP-1    | Valid positive quantity    | 100                 | Yes    |
 * | EC-DISP-2    | Zero quantity              | 0                   | Yes    |
 * | EC-DISP-3    | Negative quantity          | -1                  | No     |
 * | EC-DISP-4    | Minimum positive (1)       | 1                   | Yes    |
 * | EC-DISP-5    | Large quantity             | 10000               | Yes    |
 * -----------------------------------------------------------------
 * 
 * Field: tipologia (type/category)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-TIPO-1    | Valid non-empty string     | "Supplements"       | Yes    |
 * | EC-TIPO-2    | Empty string               | ""                  | Yes*   |
 * | EC-TIPO-3    | Null value                 | null                | Yes*   |
 * | EC-TIPO-4    | Max length string (20)     | "T".repeat(20)      | Yes    |
 * | EC-TIPO-5    | Over max length (21+)      | "T".repeat(21)      | No     |
 * -----------------------------------------------------------------
 * 
 * ============================================================================
 * BOUNDARY VALUE DESIGN (Step 2.2)
 * ============================================================================
 * 
 * Field: descrizione (maxlength="100" from JSP textarea)
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | Test Value           | Expected |
 * |--------------|----------------------------|---------------------|----------|
 * | BV-DESC-1    | Empty (length 0)           | ""                  | Accepted |
 * | BV-DESC-2    | Single char (length 1)     | "A"                 | Valid    |
 * | BV-DESC-3    | Just under max (99)        | "A".repeat(99)      | Valid    |
 * | BV-DESC-4    | Max length (100)           | "A".repeat(100)     | Valid    |
 * | BV-DESC-5    | Over max (101)             | "A".repeat(101)     | Invalid  |
 * -----------------------------------------------------------------
 * 
 * Field: costo (min="0.00", step="0.01" from JSP)
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | Test Value           | Expected |
 * |--------------|----------------------------|---------------------|----------|
 * | BV-COST-1    | Zero (minimum)             | 0.0                 | Valid    |
 * | BV-COST-2    | Just below zero            | -0.01               | Invalid  |
 * | BV-COST-3    | Minimum step               | 0.01                | Valid    |
 * | BV-COST-4    | Typical price              | 9.99                | Valid    |
 * | BV-COST-5    | Large price                | 9999.99             | Valid    |
 * | BV-COST-6    | Very large price           | 99999.99            | Valid    |
 * -----------------------------------------------------------------
 * 
 * Field: disponibilità (min="1" from JSP, but 0 should also be valid for out-of-stock)
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | Test Value           | Expected |
 * |--------------|----------------------------|---------------------|----------|
 * | BV-DISP-1    | Zero (out of stock)        | 0                   | Valid    |
 * | BV-DISP-2    | Minimum positive (1)       | 1                   | Valid    |
 * | BV-DISP-3    | Two                        | 2                   | Valid    |
 * | BV-DISP-4    | Negative                   | -1                  | Invalid  |
 * | BV-DISP-5    | Large quantity             | 10000               | Valid    |
 * | BV-DISP-6    | Max integer                | Integer.MAX_VALUE   | Valid    |
 * -----------------------------------------------------------------
 * 
 * Field: tipologia (maxlength="20" from JSP)
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | Test Value           | Expected |
 * |--------------|----------------------------|---------------------|----------|
 * | BV-TIPO-1    | Empty (length 0)           | ""                  | Accepted |
 * | BV-TIPO-2    | Single char (length 1)     | "T"                 | Valid    |
 * | BV-TIPO-3    | Max length (20)            | "T".repeat(20)      | Valid    |
 * | BV-TIPO-4    | Over max (21)              | "T".repeat(21)      | Invalid  |
 * | BV-TIPO-5    | Typical length             | "Supplements"       | Valid    |
 * -----------------------------------------------------------------
 */
@UnitTest
@DisplayName("InfoBean Unit Tests")
public class InfoBeanTest {
    
    private InfoBean info;
    
    @BeforeEach
    void setUp() {
        info = new InfoBean();
    }
    
    @Nested
    @DisplayName("Descrizione (Description) Tests")
    class DescrizioneTests {
        
        // ==================== Equivalence Class Tests ====================
        
        @Test
        @DisplayName("EC-DESC-1: Valid non-empty description is accepted")
        void testValidNonEmptyDescription() {
            info.setDescrizione("Delicious protein bar");
            assertEquals("Delicious protein bar", info.getDescrizione());
        }
        
        @Test
        @DisplayName("EC-DESC-2: Empty string description is accepted by bean")
        void testEmptyStringDescription() {
            info.setDescrizione("");
            assertEquals("", info.getDescrizione());
        }
        
        @Test
        @DisplayName("EC-DESC-3: Null description is accepted by bean")
        void testNullDescription() {
            info.setDescrizione(null);
            assertNull(info.getDescrizione());
        }
        
        @Test
        @DisplayName("EC-DESC-4: Max length string (100 chars) is valid")
        void testMaxLengthDescription() {
            String maxDesc = "A".repeat(100);
            info.setDescrizione(maxDesc);
            assertEquals(maxDesc, info.getDescrizione());
            assertEquals(100, info.getDescrizione().length());
        }
        
        @Test
        @DisplayName("EC-DESC-6: Description with newlines is valid")
        void testDescriptionWithNewlines() {
            info.setDescrizione("Line1\nLine2");
            assertEquals("Line1\nLine2", info.getDescrizione());
        }
        
        // ==================== Boundary Value Tests ====================
        
        @Test
        @DisplayName("BV-DESC-1: Empty string (length 0) boundary")
        void testEmptyStringBoundary() {
            info.setDescrizione("");
            assertEquals(0, info.getDescrizione().length());
        }
        
        @Test
        @DisplayName("BV-DESC-2: Single char (length 1) boundary")
        void testSingleCharBoundary() {
            info.setDescrizione("A");
            assertEquals(1, info.getDescrizione().length());
        }
        
        @Test
        @DisplayName("BV-DESC-3: Just under max (length 99) boundary")
        void testJustUnderMaxBoundary() {
            String desc = "A".repeat(99);
            info.setDescrizione(desc);
            assertEquals(99, info.getDescrizione().length());
        }
        
        @Test
        @DisplayName("BV-DESC-4: Max length (length 100) boundary")
        void testMaxLengthBoundary() {
            String desc = "A".repeat(100);
            info.setDescrizione(desc);
            assertEquals(100, info.getDescrizione().length());
        }
        
        @Test
        @DisplayName("BV-DESC-5: Over max length (length 101) - bean accepts but exceeds form limit")
        void testOverMaxLengthBoundary() {
            String desc = "A".repeat(101);
            info.setDescrizione(desc);
            assertEquals(101, info.getDescrizione().length());
        }
    }
    
    @Nested
    @DisplayName("Costo (Cost/Price) Tests")
    class CostoTests {
        
        // ==================== Equivalence Class Tests ====================
        
        @Test
        @DisplayName("EC-COST-1: Valid positive price is accepted")
        void testValidPositivePrice() {
            info.setCosto(9.99);
            assertEquals(9.99, info.getCosto(), 0.001);
        }
        
        @Test
        @DisplayName("EC-COST-2: Zero price is accepted")
        void testZeroPrice() {
            info.setCosto(0.0);
            assertEquals(0.0, info.getCosto(), 0.001);
        }
        
        @Test
        @DisplayName("EC-COST-3: Negative price is accepted by bean (validation elsewhere)")
        void testNegativePrice() {
            info.setCosto(-1.0);
            assertEquals(-1.0, info.getCosto(), 0.001);
        }
        
        @Test
        @DisplayName("EC-COST-4: Very small positive price is valid")
        void testVerySmallPositivePrice() {
            info.setCosto(0.01);
            assertEquals(0.01, info.getCosto(), 0.001);
        }
        
        @Test
        @DisplayName("EC-COST-5: Large price is valid")
        void testLargePrice() {
            info.setCosto(9999.99);
            assertEquals(9999.99, info.getCosto(), 0.001);
        }
        
        @Test
        @DisplayName("EC-COST-6: Price with many decimals is accepted")
        void testPriceWithManyDecimals() {
            info.setCosto(9.999);
            assertEquals(9.999, info.getCosto(), 0.0001);
        }
        
        // ==================== Boundary Value Tests ====================
        
        @Test
        @DisplayName("BV-COST-1: Zero (minimum) boundary")
        void testZeroBoundary() {
            info.setCosto(0.0);
            assertEquals(0.0, info.getCosto(), 0.001);
        }
        
        @Test
        @DisplayName("BV-COST-2: Just below zero boundary")
        void testJustBelowZeroBoundary() {
            info.setCosto(-0.01);
            assertEquals(-0.01, info.getCosto(), 0.001);
        }
        
        @Test
        @DisplayName("BV-COST-3: Minimum step boundary")
        void testMinimumStepBoundary() {
            info.setCosto(0.01);
            assertEquals(0.01, info.getCosto(), 0.001);
        }
        
        @Test
        @DisplayName("BV-COST-5: Large price boundary")
        void testLargePriceBoundary() {
            info.setCosto(9999.99);
            assertEquals(9999.99, info.getCosto(), 0.001);
        }
        
        @Test
        @DisplayName("BV-COST-6: Very large price boundary")
        void testVeryLargePriceBoundary() {
            info.setCosto(99999.99);
            assertEquals(99999.99, info.getCosto(), 0.001);
        }
    }
    
    @Nested
    @DisplayName("Disponibilità (Availability) Tests")
    class DisponibilitaTests {
        
        // ==================== Equivalence Class Tests ====================
        
        @Test
        @DisplayName("EC-DISP-1: Valid positive quantity is accepted")
        void testValidPositiveQuantity() {
            info.setDisponibilità(100);
            assertEquals(100, info.getDisponibilità());
        }
        
        @Test
        @DisplayName("EC-DISP-2: Zero quantity is accepted")
        void testZeroQuantity() {
            info.setDisponibilità(0);
            assertEquals(0, info.getDisponibilità());
        }
        
        @Test
        @DisplayName("EC-DISP-3: Negative quantity is accepted by bean (validation elsewhere)")
        void testNegativeQuantity() {
            info.setDisponibilità(-1);
            assertEquals(-1, info.getDisponibilità());
        }
        
        @Test
        @DisplayName("EC-DISP-4: Minimum positive (1) is valid")
        void testMinimumPositiveQuantity() {
            info.setDisponibilità(1);
            assertEquals(1, info.getDisponibilità());
        }
        
        @Test
        @DisplayName("EC-DISP-5: Large quantity is valid")
        void testLargeQuantity() {
            info.setDisponibilità(10000);
            assertEquals(10000, info.getDisponibilità());
        }
        
        // ==================== Boundary Value Tests ====================
        
        @Test
        @DisplayName("BV-DISP-1: Zero (out of stock) boundary")
        void testZeroBoundary() {
            info.setDisponibilità(0);
            assertEquals(0, info.getDisponibilità());
        }
        
        @Test
        @DisplayName("BV-DISP-2: Minimum positive (1) boundary")
        void testMinimumPositiveBoundary() {
            info.setDisponibilità(1);
            assertEquals(1, info.getDisponibilità());
        }
        
        @Test
        @DisplayName("BV-DISP-3: Two boundary")
        void testTwoBoundary() {
            info.setDisponibilità(2);
            assertEquals(2, info.getDisponibilità());
        }
        
        @Test
        @DisplayName("BV-DISP-4: Negative boundary")
        void testNegativeBoundary() {
            info.setDisponibilità(-1);
            assertEquals(-1, info.getDisponibilità());
        }
        
        @Test
        @DisplayName("BV-DISP-5: Large quantity boundary")
        void testLargeQuantityBoundary() {
            info.setDisponibilità(10000);
            assertEquals(10000, info.getDisponibilità());
        }
        
        @Test
        @DisplayName("BV-DISP-6: Max integer boundary")
        void testMaxIntegerBoundary() {
            info.setDisponibilità(Integer.MAX_VALUE);
            assertEquals(Integer.MAX_VALUE, info.getDisponibilità());
        }
    }
    
    @Nested
    @DisplayName("Tipologia (Type/Category) Tests")
    class TipologiaTests {
        
        // ==================== Equivalence Class Tests ====================
        
        @Test
        @DisplayName("EC-TIPO-1: Valid non-empty type is accepted")
        void testValidNonEmptyType() {
            info.setTipologia("Supplements");
            assertEquals("Supplements", info.getTipologia());
        }
        
        @Test
        @DisplayName("EC-TIPO-2: Empty string type is accepted by bean")
        void testEmptyStringType() {
            info.setTipologia("");
            assertEquals("", info.getTipologia());
        }
        
        @Test
        @DisplayName("EC-TIPO-3: Null type is accepted by bean")
        void testNullType() {
            info.setTipologia(null);
            assertNull(info.getTipologia());
        }
        
        @Test
        @DisplayName("EC-TIPO-4: Max length string (20 chars) is valid")
        void testMaxLengthType() {
            String maxType = "T".repeat(20);
            info.setTipologia(maxType);
            assertEquals(maxType, info.getTipologia());
            assertEquals(20, info.getTipologia().length());
        }
        
        // ==================== Boundary Value Tests ====================
        
        @Test
        @DisplayName("BV-TIPO-1: Empty string (length 0) boundary")
        void testEmptyStringBoundary() {
            info.setTipologia("");
            assertEquals(0, info.getTipologia().length());
        }
        
        @Test
        @DisplayName("BV-TIPO-2: Single char (length 1) boundary")
        void testSingleCharBoundary() {
            info.setTipologia("T");
            assertEquals(1, info.getTipologia().length());
        }
        
        @Test
        @DisplayName("BV-TIPO-3: Max length (length 20) boundary")
        void testMaxLengthBoundary() {
            String type = "T".repeat(20);
            info.setTipologia(type);
            assertEquals(20, info.getTipologia().length());
        }
        
        @Test
        @DisplayName("BV-TIPO-4: Over max length (length 21) - bean accepts but exceeds form limit")
        void testOverMaxLengthBoundary() {
            String type = "T".repeat(21);
            info.setTipologia(type);
            assertEquals(21, info.getTipologia().length());
        }
    }
    
    @Nested
    @DisplayName("ToString and General Tests")
    class GeneralTests {
        
        @Test
        @DisplayName("toString returns properly formatted string")
        void testToString() {
            info.setDescrizione("Test Description");
            info.setCosto(19.99);
            info.setDisponibilità(50);
            info.setTipologia("Protein");
            
            String result = info.toString();
            assertNotNull(result);
            // toString should contain the field values
            assertTrue(result.contains("Test Description") || result.contains("19.99") || result.contains("50"));
        }
        
        @Test
        @DisplayName("InfoBean can set and get all fields together")
        void testSetAndGetAllFields() {
            info.setDescrizione("Product description");
            info.setCosto(29.99);
            info.setDisponibilità(100);
            info.setTipologia("Supplements");
            
            assertAll("Info fields",
                () -> assertEquals("Product description", info.getDescrizione()),
                () -> assertEquals(29.99, info.getCosto(), 0.001),
                () -> assertEquals(100, info.getDisponibilità()),
                () -> assertEquals("Supplements", info.getTipologia())
            );
        }
    }
}
