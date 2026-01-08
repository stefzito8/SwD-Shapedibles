package model.bean;

import categories.UnitTest;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for ProductBean.
 * 
 * Testing Level: Unit
 * Technique: Black-Box (Equivalence Class Testing, Boundary Value Testing)
 * 
 * ============================================================================
 * EQUIVALENCE CLASS DESIGN (Step 2.1)
 * ============================================================================
 * 
 * Field: codice (product code - integer)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-COD-1     | Valid positive integer     | 1001                | Yes    |
 * | EC-COD-2     | Zero                       | 0                   | Yes    |
 * | EC-COD-3     | Negative value             | -1                  | Yes*   |
 * | EC-COD-4     | Large positive integer     | 999999              | Yes    |
 * | EC-COD-5     | Maximum integer            | Integer.MAX_VALUE   | Yes    |
 * | EC-COD-6     | Minimum integer            | Integer.MIN_VALUE   | Yes    |
 * -----------------------------------------------------------------
 * *Note: -1 is the default value in constructor
 * 
 * Field: nome (product name)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-NOM-1     | Valid non-empty string     | "Protein Bar"       | Yes    |
 * | EC-NOM-2     | Empty string               | ""                  | Yes*   |
 * | EC-NOM-3     | Null value                 | null                | Yes*   |
 * | EC-NOM-4     | Max length string (20)     | "B".repeat(20)      | Yes    |
 * | EC-NOM-5     | Over max length (21+)      | "B".repeat(21)      | No     |
 * | EC-NOM-6     | Single character           | "B"                 | Yes    |
 * | EC-NOM-7     | Name with special chars    | "Protein-Bar 2.0"   | Yes    |
 * -----------------------------------------------------------------
 * 
 * ============================================================================
 * BOUNDARY VALUE DESIGN (Step 2.2)
 * ============================================================================
 * 
 * Field: codice (integer boundaries)
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | Test Value           | Expected |
 * |--------------|----------------------------|---------------------|----------|
 * | BV-COD-1     | Default value (-1)         | -1                  | Valid    |
 * | BV-COD-2     | Zero (boundary)            | 0                   | Valid    |
 * | BV-COD-3     | One (first positive)       | 1                   | Valid    |
 * | BV-COD-4     | Typical value              | 1001                | Valid    |
 * | BV-COD-5     | Large value                | 999999              | Valid    |
 * | BV-COD-6     | Maximum integer            | Integer.MAX_VALUE   | Valid    |
 * -----------------------------------------------------------------
 * 
 * Field: nome (string length boundaries based on maxlength="20" from JSP)
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | Test Value           | Expected |
 * |--------------|----------------------------|---------------------|----------|
 * | BV-NOM-1     | Empty string (length 0)    | ""                  | Accepted |
 * | BV-NOM-2     | Single char (length 1)     | "B"                 | Valid    |
 * | BV-NOM-3     | Max length (length 20)     | "B".repeat(20)      | Valid    |
 * | BV-NOM-4     | Over max (length 21)       | "B".repeat(21)      | Invalid  |
 * | BV-NOM-5     | Typical length             | "Protein Bar"       | Valid    |
 * -----------------------------------------------------------------
 */
@UnitTest
@DisplayName("ProductBean Unit Tests")
public class ProductBeanTest {
    
    private ProductBean product;
    
    @BeforeEach
    void setUp() {
        product = new ProductBean();
    }
    
    @Nested
    @DisplayName("Codice (Product Code) Tests")
    class CodiceTests {
        
        // ==================== Equivalence Class Tests ====================
        
        @Test
        @DisplayName("EC-COD-1: Valid positive integer code is accepted")
        void testValidPositiveCode() {
            // Arrange & Act
            product.setCodice(1001);
            
            // Assert
            assertEquals(1001, product.getCodice());
        }
        
        @Test
        @DisplayName("EC-COD-2: Zero code is accepted")
        void testZeroCode() {
            // Arrange & Act
            product.setCodice(0);
            
            // Assert
            assertEquals(0, product.getCodice());
        }
        
        @Test
        @DisplayName("EC-COD-3: Negative value (default -1) is accepted")
        void testNegativeCode() {
            // Arrange & Act
            product.setCodice(-1);
            
            // Assert
            assertEquals(-1, product.getCodice());
        }
        
        @Test
        @DisplayName("EC-COD-4: Large positive integer is valid")
        void testLargePositiveCode() {
            // Arrange & Act
            product.setCodice(999999);
            
            // Assert
            assertEquals(999999, product.getCodice());
        }
        
        @Test
        @DisplayName("EC-COD-5: Maximum integer value is valid")
        void testMaxIntegerCode() {
            // Arrange & Act
            product.setCodice(Integer.MAX_VALUE);
            
            // Assert
            assertEquals(Integer.MAX_VALUE, product.getCodice());
        }
        
        // ==================== Boundary Value Tests ====================
        
        @Test
        @DisplayName("BV-COD-1: Default value (-1) boundary")
        void testDefaultValueBoundary() {
            product.setCodice(-1);
            assertEquals(-1, product.getCodice());
        }
        
        @Test
        @DisplayName("BV-COD-2: Zero boundary")
        void testZeroBoundary() {
            product.setCodice(0);
            assertEquals(0, product.getCodice());
        }
        
        @Test
        @DisplayName("BV-COD-3: One (first positive) boundary")
        void testOneBoundary() {
            product.setCodice(1);
            assertEquals(1, product.getCodice());
        }
        
        @Test
        @DisplayName("BV-COD-4: Typical value boundary")
        void testTypicalValueBoundary() {
            product.setCodice(1001);
            assertEquals(1001, product.getCodice());
        }
        
        @Test
        @DisplayName("BV-COD-5: Large value boundary")
        void testLargeValueBoundary() {
            product.setCodice(999999);
            assertEquals(999999, product.getCodice());
        }
        
        @Test
        @DisplayName("BV-COD-6: Maximum integer boundary")
        void testMaxIntegerBoundary() {
            product.setCodice(Integer.MAX_VALUE);
            assertEquals(Integer.MAX_VALUE, product.getCodice());
        }
    }
    
    @Nested
    @DisplayName("Nome (Product Name) Tests")
    class NomeTests {
        
        // ==================== Equivalence Class Tests ====================
        
        @Test
        @DisplayName("EC-NOM-1: Valid non-empty name is accepted")
        void testValidNonEmptyName() {
            product.setNome("Protein Bar");
            assertEquals("Protein Bar", product.getNome());
        }
        
        @Test
        @DisplayName("EC-NOM-2: Empty string name is accepted by bean")
        void testEmptyStringName() {
            product.setNome("");
            assertEquals("", product.getNome());
        }
        
        @Test
        @DisplayName("EC-NOM-3: Null name is accepted by bean")
        void testNullName() {
            product.setNome(null);
            assertNull(product.getNome());
        }
        
        @Test
        @DisplayName("EC-NOM-4: Max length string (20 chars) is valid")
        void testMaxLengthName() {
            String maxLengthName = "B".repeat(20);
            product.setNome(maxLengthName);
            assertEquals(maxLengthName, product.getNome());
            assertEquals(20, product.getNome().length());
        }
        
        @Test
        @DisplayName("EC-NOM-6: Single character name is valid")
        void testSingleCharName() {
            product.setNome("B");
            assertEquals("B", product.getNome());
        }
        
        @Test
        @DisplayName("EC-NOM-7: Name with special characters is valid")
        void testNameWithSpecialChars() {
            product.setNome("Protein-Bar 2.0");
            assertEquals("Protein-Bar 2.0", product.getNome());
        }
        
        // ==================== Boundary Value Tests ====================
        
        @Test
        @DisplayName("BV-NOM-1: Empty string (length 0) boundary")
        void testEmptyStringBoundary() {
            product.setNome("");
            assertEquals(0, product.getNome().length());
        }
        
        @Test
        @DisplayName("BV-NOM-2: Single char (length 1) boundary")
        void testSingleCharBoundary() {
            product.setNome("B");
            assertEquals(1, product.getNome().length());
        }
        
        @Test
        @DisplayName("BV-NOM-3: Max length (length 20) boundary")
        void testMaxLengthBoundary() {
            String name = "B".repeat(20);
            product.setNome(name);
            assertEquals(20, product.getNome().length());
        }
        
        @Test
        @DisplayName("BV-NOM-4: Over max length (length 21) - bean accepts but exceeds form limit")
        void testOverMaxLengthBoundary() {
            String name = "B".repeat(21);
            product.setNome(name);
            assertEquals(21, product.getNome().length());
        }
    }
    
    @Nested
    @DisplayName("Bean Serialization and General Tests")
    class GeneralTests {
        
        @Test
        @DisplayName("New ProductBean has default values")
        void testDefaultValues() {
            ProductBean newProduct = new ProductBean();
            assertEquals(-1, newProduct.getCodice());
            assertEquals(" ", newProduct.getNome());
        }
        
        @Test
        @DisplayName("ProductBean can set and get both fields together")
        void testSetAndGetBothFields() {
            product.setCodice(1001);
            product.setNome("Protein Bar");
            
            assertAll("Product fields",
                () -> assertEquals(1001, product.getCodice()),
                () -> assertEquals("Protein Bar", product.getNome())
            );
        }
        
        @Test
        @DisplayName("ProductBean fields can be updated")
        void testFieldsCanBeUpdated() {
            // Initial values
            product.setCodice(1001);
            product.setNome("Old Name");
            
            // Update values
            product.setCodice(1002);
            product.setNome("New Name");
            
            assertAll("Updated fields",
                () -> assertEquals(1002, product.getCodice()),
                () -> assertEquals("New Name", product.getNome())
            );
        }
    }
}
