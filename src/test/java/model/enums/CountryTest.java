package model.enums;

import categories.UnitTest;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for Country enum.
 * 
 * Testing Level: Unit
 * Technique: Black-Box (Equivalence Class Testing, Boundary Value Testing)
 * 
 * ============================================================================
 * EQUIVALENCE CLASS DESIGN (Step 2.1)
 * ============================================================================
 * 
 * Enum value selection partitions:
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-CSEL-1    | First enum value           | Country.USA         | Yes    |
 * | EC-CSEL-2    | Last enum value            | (last in enum)      | Yes    |
 * | EC-CSEL-3    | Middle enum value          | Country.GERMANY     | Yes    |
 * | EC-CSEL-4    | Valid valueOf() input      | "USA"               | Yes    |
 * | EC-CSEL-5    | Invalid valueOf() input    | "INVALID"           | No     |
 * -----------------------------------------------------------------
 * 
 * Display name retrieval partitions:
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value      | Valid? |
 * |--------------|-----------------------------|--------------------------|--------|
 * | EC-CNAME-1   | Simple name                | USA -> "United States"  | Yes    |
 * | EC-CNAME-2   | Multi-word name            | CZECH_REPUBLIC -> "Czech Republic" | Yes |
 * | EC-CNAME-3   | Name with special chars    | ANTIGUA_DEPS -> "Antigua & Deps"   | Yes |
 * -----------------------------------------------------------------
 * 
 * Enum operations partitions:
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Test Operation          | Valid? |
 * |--------------|-----------------------------|------------------------|--------|
 * | EC-COP-1     | values() returns all       | Country.values()       | Yes    |
 * | EC-COP-2     | ordinal() returns index    | Country.USA.ordinal()  | Yes    |
 * | EC-COP-3     | name() returns enum name   | Country.USA.name()     | Yes    |
 * | EC-COP-4     | valueOf() valid            | Country.valueOf("USA") | Yes    |
 * | EC-COP-5     | valueOf() invalid          | Country.valueOf("XXX") | No     |
 * -----------------------------------------------------------------
 * 
 * ============================================================================
 * BOUNDARY VALUE DESIGN (Step 2.2)
 * ============================================================================
 * 
 * Enum ordinal boundaries:
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | Test Value               | Expected |
 * |--------------|----------------------------|--------------------------|----------|
 * | BV-ORD-1     | First ordinal (0)          | Country.values()[0]      | USA      |
 * | BV-ORD-2     | Last ordinal (n-1)         | Country.values()[n-1]    | Last enum|
 * | BV-ORD-3     | Middle ordinal             | Country.values()[n/2]    | Valid    |
 * | BV-ORD-4     | Access at -1 (invalid)     | values()[-1]             | Exception|
 * | BV-ORD-5     | Access at n (invalid)      | values()[n]              | Exception|
 * -----------------------------------------------------------------
 * 
 * Enum values() array boundaries:
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | Test Value               | Expected     |
 * |--------------|----------------------------|--------------------------|--------------|
 * | BV-VAL-1     | Array length > 0           | values().length          | 195+ entries |
 * | BV-VAL-2     | First element not null     | values()[0]              | Not null     |
 * | BV-VAL-3     | Last element not null      | values()[length-1]       | Not null     |
 * | BV-VAL-4     | All elements unique        | distinct count == length | True         |
 * -----------------------------------------------------------------
 * 
 * valueOf() input boundaries:
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | Test Value          | Expected        |
 * |--------------|----------------------------|---------------------|-----------------|
 * | BV-VOF-1     | Valid uppercase name       | "USA"               | Country.USA     |
 * | BV-VOF-2     | Valid with underscore      | "CZECH_REPUBLIC"    | Country.CZECH_REPUBLIC |
 * | BV-VOF-3     | Lowercase (invalid)        | "usa"               | IllegalArgumentException |
 * | BV-VOF-4     | Mixed case (invalid)       | "Usa"               | IllegalArgumentException |
 * | BV-VOF-5     | Empty string               | ""                  | IllegalArgumentException |
 * | BV-VOF-6     | Null value                 | null                | NullPointerException |
 * | BV-VOF-7     | Non-existent country       | "ATLANTIS"          | IllegalArgumentException |
 * -----------------------------------------------------------------
 * 
 * Display name string boundaries:
 * -----------------------------------------------------------------
 * | Boundary ID  | Description                | Test Enum              | Expected Name       |
 * |--------------|----------------------------|------------------------|---------------------|
 * | BV-DN-1      | Shortest display name      | (find shortest)        | Not empty           |
 * | BV-DN-2      | Longest display name       | (find longest)         | Valid string        |
 * | BV-DN-3      | Name with & character      | ANTIGUA_DEPS           | "Antigua & Deps"    |
 * | BV-DN-4      | Name with spaces           | REPUBLIC_OF_CHINA      | Has spaces          |
 * -----------------------------------------------------------------
 * 
 * @see model.enums.Country
 */
@UnitTest
@DisplayName("Country Enum Unit Tests")
public class CountryTest {
    
    @Nested
    @DisplayName("Enum Value Selection Tests (EC-CSEL)")
    class EnumValueSelectionTests {
        
        @Test
        @DisplayName("EC-CSEL-1: First enum value (USA) exists and is accessible")
        void testFirstEnumValue() {
            Country first = Country.values()[0];
            assertNotNull(first);
            assertEquals("USA", first.name());
        }
        
        @Test
        @DisplayName("EC-CSEL-2: Last enum value exists and is accessible")
        void testLastEnumValue() {
            Country[] values = Country.values();
            Country last = values[values.length - 1];
            assertNotNull(last);
            assertTrue(last.ordinal() == values.length - 1);
        }
        
        @Test
        @DisplayName("EC-CSEL-3: Middle enum value (GERMANY) exists")
        void testMiddleEnumValue() {
            Country germany = Country.GERMANY;
            assertNotNull(germany);
            assertEquals("GERMANY", germany.name());
        }
        
        @Test
        @DisplayName("EC-CSEL-4: Valid valueOf() input returns correct enum")
        void testValidValueOf() {
            Country usa = Country.valueOf("USA");
            assertEquals(Country.USA, usa);
        }
        
        @Test
        @DisplayName("EC-CSEL-5: Invalid valueOf() input throws IllegalArgumentException")
        void testInvalidValueOf() {
            assertThrows(IllegalArgumentException.class, () -> {
                Country.valueOf("INVALID");
            });
        }
    }
    
    @Nested
    @DisplayName("Display Name Tests (EC-CNAME)")
    class DisplayNameTests {
        
        @Test
        @DisplayName("EC-CNAME-1: Simple name - USA returns display name")
        void testSimpleDisplayName() {
            Country usa = Country.USA;
            String displayName = usa.toString();
            assertNotNull(displayName);
            assertFalse(displayName.isEmpty());
            assertEquals("United States", displayName);
        }
        
        @Test
        @DisplayName("EC-CNAME-2: Multi-word name - CZECH_REPUBLIC has spaces in display name")
        void testMultiWordDisplayName() {
            Country czechRepublic = Country.CZECH_REPUBLIC;
            String displayName = czechRepublic.toString();
            assertNotNull(displayName);
            assertTrue(displayName.contains(" ") || displayName.length() > 0);
            assertEquals("Czech Republic", displayName);
        }
        
        @Test
        @DisplayName("EC-CNAME-3: Name with special chars - ANTIGUA_DEPS has & in display name")
        void testSpecialCharDisplayName() {
            Country antiguaDeps = Country.ANTIGUA_DEPS;
            String displayName = antiguaDeps.toString();
            assertNotNull(displayName);
            assertTrue(displayName.contains("&"));
            assertEquals("Antigua & Deps", displayName);
        }
    }
    
    @Nested
    @DisplayName("Enum Operations Tests (EC-COP)")
    class EnumOperationsTests {
        
        @Test
        @DisplayName("EC-COP-1: values() returns all enum constants")
        void testValuesReturnsAll() {
            Country[] values = Country.values();
            assertNotNull(values);
            assertTrue(values.length > 0);
            // Should have many countries (195+ based on SPEC.md)
            assertTrue(values.length >= 100, "Expected at least 100 countries");
        }
        
        @Test
        @DisplayName("EC-COP-2: ordinal() returns correct index")
        void testOrdinalReturnsIndex() {
            Country usa = Country.USA;
            assertEquals(0, usa.ordinal()); // First element has ordinal 0
        }
        
        @Test
        @DisplayName("EC-COP-3: name() returns enum constant name")
        void testNameReturnsEnumName() {
            Country usa = Country.USA;
            assertEquals("USA", usa.name());
            
            Country germany = Country.GERMANY;
            assertEquals("GERMANY", germany.name());
        }
        
        @Test
        @DisplayName("EC-COP-4: valueOf() with valid name returns correct enum")
        void testValueOfValid() {
            assertEquals(Country.GERMANY, Country.valueOf("GERMANY"));
            assertEquals(Country.FRANCE, Country.valueOf("FRANCE"));
            assertEquals(Country.ITALY, Country.valueOf("ITALY"));
        }
        
        @Test
        @DisplayName("EC-COP-5: valueOf() with invalid name throws exception")
        void testValueOfInvalid() {
            assertThrows(IllegalArgumentException.class, () -> Country.valueOf("XXX"));
            assertThrows(IllegalArgumentException.class, () -> Country.valueOf("ATLANTIS"));
        }
    }
    
    @Nested
    @DisplayName("Ordinal Boundary Tests (BV-ORD)")
    class OrdinalBoundaryTests {
        
        @Test
        @DisplayName("BV-ORD-1: First ordinal (0) is USA")
        void testFirstOrdinal() {
            Country first = Country.values()[0];
            assertEquals(0, first.ordinal());
            assertEquals(Country.USA, first);
        }
        
        @Test
        @DisplayName("BV-ORD-2: Last ordinal (n-1) is valid")
        void testLastOrdinal() {
            Country[] values = Country.values();
            int lastIndex = values.length - 1;
            Country last = values[lastIndex];
            assertEquals(lastIndex, last.ordinal());
        }
        
        @Test
        @DisplayName("BV-ORD-3: Middle ordinal is valid")
        void testMiddleOrdinal() {
            Country[] values = Country.values();
            int middleIndex = values.length / 2;
            Country middle = values[middleIndex];
            assertEquals(middleIndex, middle.ordinal());
            assertNotNull(middle.toString());
        }
        
        @Test
        @DisplayName("BV-ORD-4: Access at -1 throws ArrayIndexOutOfBoundsException")
        void testNegativeIndexAccess() {
            assertThrows(ArrayIndexOutOfBoundsException.class, () -> {
                Country[] values = Country.values();
                @SuppressWarnings("unused")
                Country invalid = values[-1];
            });
        }
        
        @Test
        @DisplayName("BV-ORD-5: Access at n throws ArrayIndexOutOfBoundsException")
        void testOutOfBoundsIndexAccess() {
            assertThrows(ArrayIndexOutOfBoundsException.class, () -> {
                Country[] values = Country.values();
                @SuppressWarnings("unused")
                Country invalid = values[values.length];
            });
        }
    }
    
    @Nested
    @DisplayName("Values Array Boundary Tests (BV-VAL)")
    class ValuesArrayBoundaryTests {
        
        @Test
        @DisplayName("BV-VAL-1: Array length is greater than 0")
        void testArrayLengthPositive() {
            Country[] values = Country.values();
            assertTrue(values.length > 0);
            assertTrue(values.length >= 100, "Expected at least 100 countries");
        }
        
        @Test
        @DisplayName("BV-VAL-2: First element is not null")
        void testFirstElementNotNull() {
            Country[] values = Country.values();
            assertNotNull(values[0]);
        }
        
        @Test
        @DisplayName("BV-VAL-3: Last element is not null")
        void testLastElementNotNull() {
            Country[] values = Country.values();
            assertNotNull(values[values.length - 1]);
        }
        
        @Test
        @DisplayName("BV-VAL-4: All elements are unique")
        void testAllElementsUnique() {
            Country[] values = Country.values();
            long distinctCount = Arrays.stream(values).distinct().count();
            assertEquals(values.length, distinctCount, "All enum values should be unique");
        }
    }
    
    @Nested
    @DisplayName("valueOf() Input Boundary Tests (BV-VOF)")
    class ValueOfInputBoundaryTests {
        
        @Test
        @DisplayName("BV-VOF-1: Valid uppercase name returns enum")
        void testValidUppercaseName() {
            Country usa = Country.valueOf("USA");
            assertEquals(Country.USA, usa);
        }
        
        @Test
        @DisplayName("BV-VOF-2: Valid name with underscore returns enum")
        void testValidNameWithUnderscore() {
            Country czechRepublic = Country.valueOf("CZECH_REPUBLIC");
            assertEquals(Country.CZECH_REPUBLIC, czechRepublic);
        }
        
        @Test
        @DisplayName("BV-VOF-3: Lowercase name throws IllegalArgumentException")
        void testLowercaseNameThrows() {
            assertThrows(IllegalArgumentException.class, () -> Country.valueOf("usa"));
        }
        
        @Test
        @DisplayName("BV-VOF-4: Mixed case name throws IllegalArgumentException")
        void testMixedCaseNameThrows() {
            assertThrows(IllegalArgumentException.class, () -> Country.valueOf("Usa"));
        }
        
        @Test
        @DisplayName("BV-VOF-5: Empty string throws IllegalArgumentException")
        void testEmptyStringThrows() {
            assertThrows(IllegalArgumentException.class, () -> Country.valueOf(""));
        }
        
        @Test
        @DisplayName("BV-VOF-6: Null value throws NullPointerException")
        void testNullValueThrows() {
            assertThrows(NullPointerException.class, () -> Country.valueOf(null));
        }
        
        @Test
        @DisplayName("BV-VOF-7: Non-existent country name throws IllegalArgumentException")
        void testNonExistentCountryThrows() {
            assertThrows(IllegalArgumentException.class, () -> Country.valueOf("ATLANTIS"));
        }
    }
    
    @Nested
    @DisplayName("Display Name Boundary Tests (BV-DN)")
    class DisplayNameBoundaryTests {
        
        @Test
        @DisplayName("BV-DN-1: All countries have non-empty display names")
        void testAllDisplayNamesNotEmpty() {
            for (Country country : Country.values()) {
                String displayName = country.toString();
                assertNotNull(displayName, "Display name for " + country.name() + " should not be null");
                assertFalse(displayName.isEmpty(), "Display name for " + country.name() + " should not be empty");
            }
        }
        
        @Test
        @DisplayName("BV-DN-2: Longest display name is valid string")
        void testLongestDisplayName() {
            String longestName = "";
            Country countryWithLongest = null;
            
            for (Country country : Country.values()) {
                String displayName = country.toString();
                if (displayName.length() > longestName.length()) {
                    longestName = displayName;
                    countryWithLongest = country;
                }
            }
            
            assertNotNull(countryWithLongest);
            assertFalse(longestName.isEmpty());
            assertTrue(longestName.length() > 0);
        }
        
        @Test
        @DisplayName("BV-DN-3: Display name with & character (ANTIGUA_DEPS)")
        void testDisplayNameWithAmpersand() {
            Country antiguaDeps = Country.ANTIGUA_DEPS;
            String displayName = antiguaDeps.toString();
            assertEquals("Antigua & Deps", displayName);
        }
        
        @Test
        @DisplayName("BV-DN-4: Display name with spaces")
        void testDisplayNameWithSpaces() {
            // Test a country that should have spaces in its display name
            Country czechRepublic = Country.CZECH_REPUBLIC;
            String displayName = czechRepublic.toString();
            assertTrue(displayName.contains(" "), "Czech Republic should have spaces in display name");
        }
    }
    
    @Nested
    @DisplayName("General Enum Tests")
    class GeneralEnumTests {
        
        @Test
        @DisplayName("All enum values have consistent ordinal and array position")
        void testOrdinalConsistency() {
            Country[] values = Country.values();
            for (int i = 0; i < values.length; i++) {
                assertEquals(i, values[i].ordinal(), 
                    "Ordinal of " + values[i].name() + " should match array index");
            }
        }
        
        @Test
        @DisplayName("Enum constants are equal to themselves")
        void testEnumEquality() {
            assertEquals(Country.USA, Country.USA);
            assertEquals(Country.GERMANY, Country.GERMANY);
            assertNotEquals(Country.USA, Country.GERMANY);
        }
        
        @Test
        @DisplayName("Enum can be used in switch statement")
        void testEnumInSwitch() {
            Country country = Country.USA;
            String result;
            
            switch (country) {
                case USA:
                    result = "United States";
                    break;
                case GERMANY:
                    result = "Germany";
                    break;
                default:
                    result = "Other";
            }
            
            assertEquals("United States", result);
        }
    }
    
    // ============================================================================
    // Mutation Killer Tests - Targets surviving mutations
    // ============================================================================
    
    @Nested
    @DisplayName("Mutation Killer Tests")
    class MutationKillerTests {
        
        @Test
        @DisplayName("getValues returns non-null array - kills NullReturnValsMutator on line 216")
        void testGetValuesNotNull() {
            String[] values = Country.getValues();
            assertNotNull(values, "getValues() must not return null");
            assertTrue(values.length > 0, "getValues() must return non-empty array");
        }
        
        @Test
        @DisplayName("getValues returns array with correct first element")
        void testGetValuesFirstElement() {
            String[] values = Country.getValues();
            // First element should be the display name of first enum constant
            assertEquals(Country.values()[0].toString(), values[0]);
        }
        
        @Test
        @DisplayName("getValues returns array with all elements - verifies stream mapping works")
        void testGetValuesContainsAllCountries() {
            String[] values = Country.getValues();
            assertEquals(Country.values().length, values.length, 
                "getValues() array length must match number of enum constants");
            
            // Verify some specific values are present
            assertTrue(Arrays.asList(values).contains("United States"));
            assertTrue(Arrays.asList(values).contains("Germany"));
            assertTrue(Arrays.asList(values).contains("Zimbabwe"));
        }
        
        @Test
        @DisplayName("getValues returns new array each time - defensive copy")
        void testGetValuesDefensiveCopy() {
            String[] values1 = Country.getValues();
            String[] values2 = Country.getValues();
            assertNotSame(values1, values2, "getValues() should return new array each call");
            assertArrayEquals(values1, values2, "Arrays should have same content");
        }
    }
}
