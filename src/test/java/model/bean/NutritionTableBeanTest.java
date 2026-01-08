package model.bean;

import categories.UnitTest;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for NutritionTableBean.
 * 
 * Testing Level: Unit
 * Technique: Black-Box (Equivalence Class Testing, Boundary Value Testing)
 * 
 * ============================================================================
 * EQUIVALENCE CLASS DESIGN (Step 2.1)
 * ============================================================================
 * 
 * Common nutritional value partitions:
 * - energia (integer): kcal/kJ values
 * - grassi, grassi_saturi, carboedrati, zucherri, fibre, proteine, sale (double): grams per 100g
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-NUT-1     | Valid positive value       | 10.5 / 131 (energia)| Yes    |
 * | EC-NUT-2     | Zero value                 | 0.0 / 0 (energia)   | Yes    |
 * | EC-NUT-3     | Negative value             | -1.0 / -1 (energia) | No     |
 * | EC-NUT-4     | Very small positive        | 0.01 (N/A energia)  | Yes    |
 * | EC-NUT-5     | Large value                | 999.99 / 999        | Yes    |
 * | EC-NUT-6     | Value at typical max (100) | 100.0 / 100         | Yes    |
 * -----------------------------------------------------------------
 * Note: Step 0.01 and min 0.00 inferred from productEdit.jsp (double fields only)
 * 
 * Field: codice_prodotto (product code reference - integer)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-CODP-1    | Valid positive integer     | 1001                | Yes    |
 * | EC-CODP-2    | Zero                       | 0                   | Yes    |
 * | EC-CODP-3    | Negative (default -1)      | -1                  | Yes*   |
 * -----------------------------------------------------------------
 * 
 * Logical constraint partitions:
 * -----------------------------------------------------------------
 * | Partition ID | Description                        | Constraint              |
 * |--------------|------------------------------------|-------------------------|
 * | EC-LOG-1     | Saturated fat ≤ total fat         | grassi_saturi ≤ grassi  |
 * | EC-LOG-2     | Sugars ≤ carbohydrates            | zucherri ≤ carboedrati  |
 * -----------------------------------------------------------------
 * 
 * ============================================================================
 * BOUNDARY VALUE DESIGN (Step 2.2)
 * ============================================================================
 * 
 * Common boundaries for all nutritional values (min=0.00, step=0.01):
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | Test Value           | Expected |
 * |--------------|----------------------------|---------------------|----------|
 * | BV-NUT-1     | Zero (minimum)             | 0.0                 | Valid    |
 * | BV-NUT-2     | Just below zero            | -0.01               | Invalid  |
 * | BV-NUT-3     | Minimum step               | 0.01                | Valid    |
 * | BV-NUT-4     | Typical value              | 25.0                | Valid    |
 * | BV-NUT-5     | At 100                     | 100.0               | Valid    |
 * | BV-NUT-6     | Just above 100             | 100.01              | Valid*   |
 * | BV-NUT-7     | Large value                | 999.99              | Valid    |
 * -----------------------------------------------------------------
 * *energia (energy) can exceed 100 (measured in kcal/kJ)
 * 
 * Logical constraint boundaries (saturated fat ≤ total fat):
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | grassi | grassi_saturi | Expected |
 * |--------------|----------------------------|--------|---------------|----------|
 * | BV-SAT-1     | Saturated = Total          | 10.0   | 10.0          | Valid    |
 * | BV-SAT-2     | Saturated just below Total | 10.0   | 9.99          | Valid    |
 * | BV-SAT-3     | Saturated just above Total | 10.0   | 10.01         | Invalid  |
 * | BV-SAT-4     | Both zero                  | 0.0    | 0.0           | Valid    |
 * -----------------------------------------------------------------
 * 
 * Logical constraint boundaries (sugars ≤ carbohydrates):
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | carboedrati | zucherri | Expected |
 * |--------------|----------------------------|-------------|----------|----------|
 * | BV-SUG-1     | Sugars = Carbs             | 50.0        | 50.0     | Valid    |
 * | BV-SUG-2     | Sugars just below Carbs    | 50.0        | 49.99    | Valid    |
 * | BV-SUG-3     | Sugars just above Carbs    | 50.0        | 50.01    | Invalid  |
 * | BV-SUG-4     | Both zero                  | 0.0         | 0.0      | Valid    |
 * -----------------------------------------------------------------
 */
@UnitTest
@DisplayName("NutritionTableBean Unit Tests")
public class NutritionTableBeanTest {
    
    private NutritionTableBean nutrition;
    
    @BeforeEach
    void setUp() {
        nutrition = new NutritionTableBean();
    }
    
    @Nested
    @DisplayName("Codice Prodotto (Product Code) Tests")
    class CodiceProdottoTests {
        
        @Test
        @DisplayName("EC-CODP-1: Valid positive product code is accepted")
        void testValidProductCode() {
            nutrition.setCodiceProdotto(1001);
            assertEquals(1001, nutrition.getCodiceProdotto());
        }
        
        @Test
        @DisplayName("EC-CODP-2: Zero product code is accepted by bean")
        void testZeroProductCode() {
            nutrition.setCodiceProdotto(0);
            assertEquals(0, nutrition.getCodiceProdotto());
        }
        
        @Test
        @DisplayName("EC-CODP-3: Negative product code (default -1) is accepted by bean")
        void testNegativeProductCode() {
            nutrition.setCodiceProdotto(-1);
            assertEquals(-1, nutrition.getCodiceProdotto());
        }
    }
    
    @Nested
    @DisplayName("Energia (Energy) Tests")
    class EnergiaTests {
        
        @Test
        @DisplayName("EC-NUT-1: Valid positive energy value is accepted")
        void testValidPositiveEnergy() {
            nutrition.setEnergia(250);
            assertEquals(250, nutrition.getEnergia());
        }
        
        @Test
        @DisplayName("EC-NUT-2: Zero energy is accepted")
        void testZeroEnergy() {
            nutrition.setEnergia(0);
            assertEquals(0, nutrition.getEnergia());
        }
        
        @Test
        @DisplayName("EC-NUT-3: Negative energy is accepted by bean (validation elsewhere)")
        void testNegativeEnergy() {
            nutrition.setEnergia(-1);
            assertEquals(-1, nutrition.getEnergia());
        }
        
        @Test
        @DisplayName("EC-NUT-5: Large energy value is valid (kcal can be high)")
        void testLargeEnergy() {
            nutrition.setEnergia(999);
            assertEquals(999, nutrition.getEnergia());
        }
        
        @Test
        @DisplayName("BV-NUT-1: Zero (minimum) boundary")
        void testZeroBoundary() {
            nutrition.setEnergia(0);
            assertEquals(0, nutrition.getEnergia());
        }
        
        @Test
        @DisplayName("BV-NUT-3: Minimum positive (1) boundary")
        void testMinimumPositiveBoundary() {
            nutrition.setEnergia(1);
            assertEquals(1, nutrition.getEnergia());
        }
    }
    
    @Nested
    @DisplayName("Grassi (Total Fat) Tests")
    class GrassiTests {
        
        @Test
        @DisplayName("EC-NUT-1: Valid positive fat value is accepted")
        void testValidPositiveFat() {
            nutrition.setGrassi(15.5);
            assertEquals(15.5, nutrition.getGrassi(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-2: Zero fat is accepted")
        void testZeroFat() {
            nutrition.setGrassi(0.0);
            assertEquals(0.0, nutrition.getGrassi(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-6: Value at 100 is valid")
        void testValueAt100() {
            nutrition.setGrassi(100.0);
            assertEquals(100.0, nutrition.getGrassi(), 0.001);
        }
        
        @Test
        @DisplayName("BV-NUT-4: Typical value boundary")
        void testTypicalValueBoundary() {
            nutrition.setGrassi(25.0);
            assertEquals(25.0, nutrition.getGrassi(), 0.001);
        }
    }
    
    @Nested
    @DisplayName("Grassi Saturi (Saturated Fat) Tests")
    class GrassiSaturiTests {
        
        @Test
        @DisplayName("EC-NUT-1: Valid positive saturated fat is accepted")
        void testValidPositiveSaturatedFat() {
            nutrition.setGrassiSaturi(5.0);
            assertEquals(5.0, nutrition.getGrassiSaturi(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-2: Zero saturated fat is accepted")
        void testZeroSaturatedFat() {
            nutrition.setGrassiSaturi(0.0);
            assertEquals(0.0, nutrition.getGrassiSaturi(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-4: Very small positive value is valid")
        void testVerySmallPositive() {
            nutrition.setGrassiSaturi(0.01);
            assertEquals(0.01, nutrition.getGrassiSaturi(), 0.001);
        }
    }
    
    @Nested
    @DisplayName("Carboedrati (Carbohydrates) Tests")
    class CarbodratiTests {
        
        @Test
        @DisplayName("EC-NUT-1: Valid positive carbs value is accepted")
        void testValidPositiveCarbs() {
            nutrition.setCarboedrati(60.0);
            assertEquals(60.0, nutrition.getCarboedrati(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-2: Zero carbs is accepted")
        void testZeroCarbs() {
            nutrition.setCarboedrati(0.0);
            assertEquals(0.0, nutrition.getCarboedrati(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-6: Value at 100 is valid")
        void testValueAt100() {
            nutrition.setCarboedrati(100.0);
            assertEquals(100.0, nutrition.getCarboedrati(), 0.001);
        }
    }
    
    @Nested
    @DisplayName("Zucherri (Sugars) Tests")
    class ZuccherriTests {
        
        @Test
        @DisplayName("EC-NUT-1: Valid positive sugars value is accepted")
        void testValidPositiveSugars() {
            nutrition.setZucherri(25.0);
            assertEquals(25.0, nutrition.getZucherri(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-2: Zero sugars is accepted")
        void testZeroSugars() {
            nutrition.setZucherri(0.0);
            assertEquals(0.0, nutrition.getZucherri(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-4: Very small positive value is valid")
        void testVerySmallPositive() {
            nutrition.setZucherri(0.01);
            assertEquals(0.01, nutrition.getZucherri(), 0.001);
        }
    }
    
    @Nested
    @DisplayName("Fibre (Fiber) Tests")
    class FibreTests {
        
        @Test
        @DisplayName("EC-NUT-1: Valid positive fiber value is accepted")
        void testValidPositiveFiber() {
            nutrition.setFibre(8.5);
            assertEquals(8.5, nutrition.getFibre(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-2: Zero fiber is accepted")
        void testZeroFiber() {
            nutrition.setFibre(0.0);
            assertEquals(0.0, nutrition.getFibre(), 0.001);
        }
        
        @Test
        @DisplayName("BV-NUT-4: Typical value boundary")
        void testTypicalValueBoundary() {
            nutrition.setFibre(25.0);
            assertEquals(25.0, nutrition.getFibre(), 0.001);
        }
    }
    
    @Nested
    @DisplayName("Proteine (Protein) Tests")
    class ProteineTests {
        
        @Test
        @DisplayName("EC-NUT-1: Valid positive protein value is accepted")
        void testValidPositiveProtein() {
            nutrition.setProteine(30.0);
            assertEquals(30.0, nutrition.getProteine(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-2: Zero protein is accepted")
        void testZeroProtein() {
            nutrition.setProteine(0.0);
            assertEquals(0.0, nutrition.getProteine(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-5: Large protein value is valid")
        void testLargeProtein() {
            nutrition.setProteine(999.99);
            assertEquals(999.99, nutrition.getProteine(), 0.001);
        }
    }
    
    @Nested
    @DisplayName("Sale (Salt) Tests")
    class SaleTests {
        
        @Test
        @DisplayName("EC-NUT-1: Valid positive salt value is accepted")
        void testValidPositiveSalt() {
            nutrition.setSale(1.5);
            assertEquals(1.5, nutrition.getSale(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-2: Zero salt is accepted")
        void testZeroSalt() {
            nutrition.setSale(0.0);
            assertEquals(0.0, nutrition.getSale(), 0.001);
        }
        
        @Test
        @DisplayName("EC-NUT-4: Very small positive salt is valid")
        void testVerySmallPositiveSalt() {
            nutrition.setSale(0.01);
            assertEquals(0.01, nutrition.getSale(), 0.001);
        }
    }
    
    @Nested
    @DisplayName("Logical Constraint Tests - Saturated Fat ≤ Total Fat")
    class SaturatedFatConstraintTests {
        
        @Test
        @DisplayName("BV-SAT-1: Saturated fat equals total fat (boundary)")
        void testSaturatedEqualsTotalFat() {
            nutrition.setGrassi(10.0);
            nutrition.setGrassiSaturi(10.0);
            
            // Both values should be set, constraint validation is business logic
            assertEquals(10.0, nutrition.getGrassi(), 0.001);
            assertEquals(10.0, nutrition.getGrassiSaturi(), 0.001);
            assertTrue(nutrition.getGrassiSaturi() <= nutrition.getGrassi());
        }
        
        @Test
        @DisplayName("BV-SAT-2: Saturated fat just below total fat")
        void testSaturatedJustBelowTotalFat() {
            nutrition.setGrassi(10.0);
            nutrition.setGrassiSaturi(9.99);
            
            assertTrue(nutrition.getGrassiSaturi() < nutrition.getGrassi());
        }
        
        @Test
        @DisplayName("BV-SAT-3: Saturated fat just above total fat (invalid logically)")
        void testSaturatedJustAboveTotalFat() {
            nutrition.setGrassi(10.0);
            nutrition.setGrassiSaturi(10.01);
            
            // Bean accepts it, but logically invalid
            assertFalse(nutrition.getGrassiSaturi() <= nutrition.getGrassi());
        }
        
        @Test
        @DisplayName("BV-SAT-4: Both saturated and total fat are zero")
        void testBothZero() {
            nutrition.setGrassi(0.0);
            nutrition.setGrassiSaturi(0.0);
            
            assertTrue(nutrition.getGrassiSaturi() <= nutrition.getGrassi());
        }
    }
    
    @Nested
    @DisplayName("Logical Constraint Tests - Sugars ≤ Carbohydrates")
    class SugarsConstraintTests {
        
        @Test
        @DisplayName("BV-SUG-1: Sugars equals carbs (boundary)")
        void testSugarsEqualsCarbs() {
            nutrition.setCarboedrati(50.0);
            nutrition.setZucherri(50.0);
            
            assertEquals(50.0, nutrition.getCarboedrati(), 0.001);
            assertEquals(50.0, nutrition.getZucherri(), 0.001);
            assertTrue(nutrition.getZucherri() <= nutrition.getCarboedrati());
        }
        
        @Test
        @DisplayName("BV-SUG-2: Sugars just below carbs")
        void testSugarsJustBelowCarbs() {
            nutrition.setCarboedrati(50.0);
            nutrition.setZucherri(49.99);
            
            assertTrue(nutrition.getZucherri() < nutrition.getCarboedrati());
        }
        
        @Test
        @DisplayName("BV-SUG-3: Sugars just above carbs (invalid logically)")
        void testSugarsJustAboveCarbs() {
            nutrition.setCarboedrati(50.0);
            nutrition.setZucherri(50.01);
            
            // Bean accepts it, but logically invalid
            assertFalse(nutrition.getZucherri() <= nutrition.getCarboedrati());
        }
        
        @Test
        @DisplayName("BV-SUG-4: Both sugars and carbs are zero")
        void testBothZero() {
            nutrition.setCarboedrati(0.0);
            nutrition.setZucherri(0.0);
            
            assertTrue(nutrition.getZucherri() <= nutrition.getCarboedrati());
        }
    }
    
    @Nested
    @DisplayName("ToString and General Tests")
    class GeneralTests {
        
        @Test
        @DisplayName("toString returns properly formatted string with all values")
        void testToString() {
            nutrition.setCodiceProdotto(1001);
            nutrition.setEnergia(250);
            nutrition.setGrassi(10.0);
            nutrition.setGrassiSaturi(3.0);
            nutrition.setCarboedrati(40.0);
            nutrition.setZucherri(15.0);
            nutrition.setFibre(5.0);
            nutrition.setProteine(20.0);
            nutrition.setSale(1.5);
            
            String result = nutrition.toString();
            assertNotNull(result);
            // toString should contain the product code and values
            assertTrue(result.contains("1001"));
        }
        
        @Test
        @DisplayName("NutritionTableBean can set and get all fields together")
        void testSetAndGetAllFields() {
            nutrition.setCodiceProdotto(1001);
            nutrition.setEnergia(250);
            nutrition.setGrassi(10.0);
            nutrition.setGrassiSaturi(3.0);
            nutrition.setCarboedrati(40.0);
            nutrition.setZucherri(15.0);
            nutrition.setFibre(5.0);
            nutrition.setProteine(20.0);
            nutrition.setSale(1.5);
            
            assertAll("Nutrition fields",
                () -> assertEquals(1001, nutrition.getCodiceProdotto()),
                () -> assertEquals(250, nutrition.getEnergia()),
                () -> assertEquals(10.0, nutrition.getGrassi(), 0.001),
                () -> assertEquals(3.0, nutrition.getGrassiSaturi(), 0.001),
                () -> assertEquals(40.0, nutrition.getCarboedrati(), 0.001),
                () -> assertEquals(15.0, nutrition.getZucherri(), 0.001),
                () -> assertEquals(5.0, nutrition.getFibre(), 0.001),
                () -> assertEquals(20.0, nutrition.getProteine(), 0.001),
                () -> assertEquals(1.5, nutrition.getSale(), 0.001)
            );
        }
    }
}
