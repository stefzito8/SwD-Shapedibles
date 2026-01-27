package model.enums;

import categories.UnitTest;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for Gender enum.
 * 
 * Testing Level: Unit
 * Technique: Black-Box (Equivalence Class Testing, Boundary Value Testing)
 * 
 * These tests target surviving mutations in Gender enum:
 * - NullReturnValsMutator on getValues() line 17
 * - EmptyObjectReturnValsMutator on toString() line 26
 */
@UnitTest
@DisplayName("Gender Enum Unit Tests")
public class GenderTest {

    @Nested
    @DisplayName("Basic Enum Tests")
    class BasicEnumTests {

        @Test
        @DisplayName("Gender enum has exactly 3 values")
        void testGenderEnumSize() {
            Gender[] values = Gender.values();
            assertEquals(3, values.length);
        }

        @Test
        @DisplayName("Gender values are in correct order")
        void testGenderOrder() {
            Gender[] values = Gender.values();
            assertEquals(Gender.MASCHIO, values[0]);
            assertEquals(Gender.FEMMINA, values[1]);
            assertEquals(Gender.ALTRO, values[2]);
        }

        @Test
        @DisplayName("Gender ordinals are correct")
        void testGenderOrdinals() {
            assertEquals(0, Gender.MASCHIO.ordinal());
            assertEquals(1, Gender.FEMMINA.ordinal());
            assertEquals(2, Gender.ALTRO.ordinal());
        }

        @Test
        @DisplayName("valueOf works for all gender values")
        void testValueOf() {
            assertEquals(Gender.MASCHIO, Gender.valueOf("MASCHIO"));
            assertEquals(Gender.FEMMINA, Gender.valueOf("FEMMINA"));
            assertEquals(Gender.ALTRO, Gender.valueOf("ALTRO"));
        }

        @Test
        @DisplayName("valueOf throws exception for invalid value")
        void testValueOfInvalid() {
            assertThrows(IllegalArgumentException.class, () -> Gender.valueOf("INVALID"));
        }
    }

    @Nested
    @DisplayName("toString Tests - Kills EmptyObjectReturnValsMutator")
    class ToStringTests {

        @Test
        @DisplayName("MASCHIO toString returns 'Maschio'")
        void testMaschioToString() {
            String result = Gender.MASCHIO.toString();
            assertEquals("Maschio", result);
            assertFalse(result.isEmpty());
            assertNotNull(result);
        }

        @Test
        @DisplayName("FEMMINA toString returns 'Femmina'")
        void testFemminaToString() {
            String result = Gender.FEMMINA.toString();
            assertEquals("Femmina", result);
            assertFalse(result.isEmpty());
        }

        @Test
        @DisplayName("ALTRO toString returns 'Altro'")
        void testAltroToString() {
            String result = Gender.ALTRO.toString();
            assertEquals("Altro", result);
            assertFalse(result.isEmpty());
        }

        @Test
        @DisplayName("All gender toString values are unique")
        void testToStringUnique() {
            String maschio = Gender.MASCHIO.toString();
            String femmina = Gender.FEMMINA.toString();
            String altro = Gender.ALTRO.toString();
            
            assertNotEquals(maschio, femmina);
            assertNotEquals(maschio, altro);
            assertNotEquals(femmina, altro);
        }

        @Test
        @DisplayName("toString returns display name not enum name")
        void testToStringIsDisplayName() {
            // Display name should be different from enum name (capitalization)
            assertEquals("Maschio", Gender.MASCHIO.toString());
            assertEquals("MASCHIO", Gender.MASCHIO.name());
            assertNotEquals(Gender.MASCHIO.name(), Gender.MASCHIO.toString());
        }
    }

    @Nested
    @DisplayName("getValues Tests - Kills NullReturnValsMutator")
    class GetValuesTests {

        @Test
        @DisplayName("getValues returns non-null array")
        void testGetValuesNotNull() {
            String[] values = Gender.getValues();
            assertNotNull(values, "getValues() must not return null");
        }

        @Test
        @DisplayName("getValues returns array with correct size")
        void testGetValuesSize() {
            String[] values = Gender.getValues();
            assertEquals(3, values.length, "getValues() must return 3 elements");
        }

        @Test
        @DisplayName("getValues returns display names not enum names")
        void testGetValuesAreDisplayNames() {
            String[] values = Gender.getValues();
            assertTrue(Arrays.asList(values).contains("Maschio"));
            assertTrue(Arrays.asList(values).contains("Femmina"));
            assertTrue(Arrays.asList(values).contains("Altro"));
            
            // Should NOT contain enum names
            assertFalse(Arrays.asList(values).contains("MASCHIO"));
            assertFalse(Arrays.asList(values).contains("FEMMINA"));
            assertFalse(Arrays.asList(values).contains("ALTRO"));
        }

        @Test
        @DisplayName("getValues returns array in correct order")
        void testGetValuesOrder() {
            String[] values = Gender.getValues();
            assertEquals("Maschio", values[0]);
            assertEquals("Femmina", values[1]);
            assertEquals("Altro", values[2]);
        }

        @Test
        @DisplayName("getValues returns defensive copy - different array each call")
        void testGetValuesDefensiveCopy() {
            String[] values1 = Gender.getValues();
            String[] values2 = Gender.getValues();
            assertNotSame(values1, values2, "getValues() should return new array each time");
            assertArrayEquals(values1, values2, "Arrays should have same content");
        }

        @Test
        @DisplayName("getValues array matches Gender.values() length")
        void testGetValuesMatchesEnumValues() {
            String[] stringValues = Gender.getValues();
            Gender[] enumValues = Gender.values();
            assertEquals(enumValues.length, stringValues.length);
            
            // Each position should match toString
            for (int i = 0; i < enumValues.length; i++) {
                assertEquals(enumValues[i].toString(), stringValues[i]);
            }
        }
    }

    @Nested
    @DisplayName("Mutation Killer Tests")
    class MutationKillerTests {

        @Test
        @DisplayName("Verify stream mapping in getValues works correctly")
        void testStreamMappingInGetValues() {
            String[] values = Gender.getValues();
            
            // Verify no null elements
            for (String value : values) {
                assertNotNull(value, "No element in getValues() should be null");
                assertFalse(value.isEmpty(), "No element in getValues() should be empty");
            }
        }

        @Test
        @DisplayName("getValues produces usable array for forms")
        void testGetValuesUsableForForms() {
            String[] values = Gender.getValues();
            
            // Can iterate without exception
            int count = 0;
            for (String value : values) {
                count++;
                assertTrue(value.length() > 0);
            }
            assertEquals(3, count);
        }

        @Test
        @DisplayName("All getValues elements start with capital letter")
        void testGetValuesCapitalization() {
            String[] values = Gender.getValues();
            for (String value : values) {
                assertTrue(Character.isUpperCase(value.charAt(0)), 
                    "Display name should start with capital: " + value);
            }
        }
    }
}
