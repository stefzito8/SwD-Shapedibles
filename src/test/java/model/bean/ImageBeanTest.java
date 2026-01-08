package model.bean;

import categories.UnitTest;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for ImageBean.
 * 
 * Testing Level: Unit
 * Technique: Black-Box (Equivalence Class, Boundary Value) + Branch Coverage
 * 
 * ============================================================================
 * EQUIVALENCE CLASS DESIGN
 * ============================================================================
 * 
 * Field: numImage (int)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value | Valid? |
 * |--------------|-----------------------------|---------------------|--------|
 * | EC-NUM-1     | Default value              | 0                   | Yes    |
 * | EC-NUM-2     | Valid positive             | 5                   | Yes    |
 * | EC-NUM-3     | Negative                   | -1                  | Yes*   |
 * -----------------------------------------------------------------
 * 
 * Field: img (String)
 * -----------------------------------------------------------------
 * | Partition ID | Description                | Representative Value       | Valid? |
 * |--------------|-----------------------------|-----------------------------|--------|
 * | EC-IMG-1     | Default value              | " "                         | Yes    |
 * | EC-IMG-2     | Valid image path           | "/images/product.jpg"       | Yes    |
 * | EC-IMG-3     | Null value                 | null                        | Yes*   |
 * | EC-IMG-4     | Empty string               | ""                          | Yes*   |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@UnitTest
@DisplayName("ImageBean Unit Tests")
public class ImageBeanTest {

    private ImageBean imageBean;

    @BeforeEach
    void setUp() {
        imageBean = new ImageBean();
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
            ImageBean bean = new ImageBean();
            assertNotNull(bean);
            assertEquals(0, bean.getNumImage());
            assertEquals(" ", bean.getImg());
            assertEquals(0, bean.getCodiceProdotto());
        }
    }

    // ============================================================================
    // NumImage Tests
    // ============================================================================

    @Nested
    @DisplayName("NumImage Tests")
    class NumImageTests {

        @Test
        @DisplayName("EC-NUM-1: Verify default numImage = 0")
        void testDefaultNumImage() {
            assertEquals(0, imageBean.getNumImage());
        }

        @Test
        @DisplayName("EC-NUM-2: Set and get valid positive numImage")
        void testValidNumImage() {
            imageBean.setNumImage(5);
            assertEquals(5, imageBean.getNumImage());
        }

        @Test
        @DisplayName("EC-NUM-3: Set negative numImage")
        void testNegativeNumImage() {
            imageBean.setNumImage(-1);
            assertEquals(-1, imageBean.getNumImage());
        }

        @Test
        @DisplayName("BV: numImage = 1")
        void testOneNumImage() {
            imageBean.setNumImage(1);
            assertEquals(1, imageBean.getNumImage());
        }

        @Test
        @DisplayName("BV: large numImage")
        void testLargeNumImage() {
            imageBean.setNumImage(999);
            assertEquals(999, imageBean.getNumImage());
        }
    }

    // ============================================================================
    // Img Tests
    // ============================================================================

    @Nested
    @DisplayName("Img Tests")
    class ImgTests {

        @Test
        @DisplayName("EC-IMG-1: Verify default img")
        void testDefaultImg() {
            assertEquals(" ", imageBean.getImg());
        }

        @Test
        @DisplayName("EC-IMG-2: Set and get valid image path")
        void testValidImg() {
            imageBean.setImg("/images/product.jpg");
            assertEquals("/images/product.jpg", imageBean.getImg());
        }

        @Test
        @DisplayName("EC-IMG-3: Set null img")
        void testNullImg() {
            imageBean.setImg(null);
            assertNull(imageBean.getImg());
        }

        @Test
        @DisplayName("EC-IMG-4: Set empty img")
        void testEmptyImg() {
            imageBean.setImg("");
            assertEquals("", imageBean.getImg());
        }

        @Test
        @DisplayName("Image path with special characters")
        void testSpecialCharImg() {
            imageBean.setImg("/images/product-1_thumb.png");
            assertEquals("/images/product-1_thumb.png", imageBean.getImg());
        }

        @Test
        @DisplayName("Long image path")
        void testLongImg() {
            String longPath = "/assets/images/products/category/subcategory/product-name-variant-size.jpg";
            imageBean.setImg(longPath);
            assertEquals(longPath, imageBean.getImg());
        }
    }

    // ============================================================================
    // CodiceProdotto Tests
    // ============================================================================

    @Nested
    @DisplayName("CodiceProdotto Tests")
    class CodiceProdottoTests {

        @Test
        @DisplayName("Verify default codiceProdotto = 0")
        void testDefaultCodiceProdotto() {
            assertEquals(0, imageBean.getCodiceProdotto());
        }

        @Test
        @DisplayName("Set and get valid positive codiceProdotto")
        void testValidCodiceProdotto() {
            imageBean.setCodiceProdotto(100);
            assertEquals(100, imageBean.getCodiceProdotto());
        }

        @Test
        @DisplayName("Set codiceProdotto = 1")
        void testOneCodiceProdotto() {
            imageBean.setCodiceProdotto(1);
            assertEquals(1, imageBean.getCodiceProdotto());
        }

        @Test
        @DisplayName("Set negative codiceProdotto")
        void testNegativeCodiceProdotto() {
            imageBean.setCodiceProdotto(-1);
            assertEquals(-1, imageBean.getCodiceProdotto());
        }

        @Test
        @DisplayName("Set large codiceProdotto")
        void testLargeCodiceProdotto() {
            imageBean.setCodiceProdotto(999999);
            assertEquals(999999, imageBean.getCodiceProdotto());
        }
    }

    // ============================================================================
    // GetImgIfString Tests (Branch Coverage)
    // ============================================================================

    @Nested
    @DisplayName("GetImgIfString Tests")
    class GetImgIfStringTests {

        @Test
        @DisplayName("B1-True: Returns img when string is contained")
        void testImgContainsString() {
            imageBean.setImg("/images/product-thumb.jpg");
            String result = imageBean.getImgIfString("thumb");
            assertEquals("/images/product-thumb.jpg", result);
        }

        @Test
        @DisplayName("B1-False: Returns null when string is not contained")
        void testImgNotContainsString() {
            imageBean.setImg("/images/product-large.jpg");
            String result = imageBean.getImgIfString("thumb");
            assertNull(result);
        }

        @Test
        @DisplayName("String at beginning")
        void testStringAtBeginning() {
            imageBean.setImg("/images/product.jpg");
            String result = imageBean.getImgIfString("/images");
            assertEquals("/images/product.jpg", result);
        }

        @Test
        @DisplayName("String at end")
        void testStringAtEnd() {
            imageBean.setImg("/images/product.jpg");
            String result = imageBean.getImgIfString(".jpg");
            assertEquals("/images/product.jpg", result);
        }

        @Test
        @DisplayName("Empty search string")
        void testEmptySearchString() {
            imageBean.setImg("/images/product.jpg");
            String result = imageBean.getImgIfString("");
            assertEquals("/images/product.jpg", result);
        }

        @Test
        @DisplayName("Case sensitive search")
        void testCaseSensitive() {
            imageBean.setImg("/images/Product.jpg");
            String result = imageBean.getImgIfString("product");
            assertNull(result); // Should be case sensitive
        }

        @Test
        @DisplayName("Exact match")
        void testExactMatch() {
            imageBean.setImg("test.jpg");
            String result = imageBean.getImgIfString("test.jpg");
            assertEquals("test.jpg", result);
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
            imageBean.setNumImage(1);
            imageBean.setCodiceProdotto(100);
            imageBean.setImg("/images/product.jpg");
            
            String result = imageBean.toString();
            assertEquals("1 100 /images/product.jpg", result);
        }

        @Test
        @DisplayName("toString with default values")
        void testToStringDefaults() {
            String result = imageBean.toString();
            assertEquals("0 0  ", result);
        }

        @Test
        @DisplayName("toString with custom values")
        void testToStringCustom() {
            imageBean.setNumImage(5);
            imageBean.setCodiceProdotto(200);
            imageBean.setImg("custom.png");
            
            String result = imageBean.toString();
            assertEquals("5 200 custom.png", result);
        }
    }
}
