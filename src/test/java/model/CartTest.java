package model;

import categories.UnitTest;
import model.bean.ProductBean;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.Collection;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for Cart model class.
 * 
 * Testing Level: Unit
 * Technique: White-Box (Branch Coverage, Loop Boundary Testing)
 * 
 * ============================================================================
 * BRANCH STRUCTURE
 * ============================================================================
 * 
 * Method: addProduct(ProductBean)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | CART-B1   | product exists in cart       | Increment qty     | Add with qty=1 |
 * -----------------------------------------------------------------
 * 
 * Method: deleteProduct(ProductBean)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | CART-B2   | products.containsKey(product)| Process delete    | Do nothing     |
 * | CART-B3   | quantity > 0 after decrement | Update quantity   | Remove product |
 * -----------------------------------------------------------------
 * 
 * Method: getProductQuantity(ProductBean)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                    | True Path         | False Path     |
 * |-----------|------------------------------|-------------------|----------------|
 * | CART-B4   | product exists               | Return quantity   | Return 0       |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@UnitTest
@DisplayName("Cart Model Unit Tests")
public class CartTest {

    private Cart cart;
    private ProductBean product1;
    private ProductBean product2;
    private ProductBean product3;

    @BeforeEach
    void setUp() {
        cart = new Cart();
        
        product1 = new ProductBean();
        product1.setCodice(1);
        product1.setNome("Product 1");
        
        product2 = new ProductBean();
        product2.setCodice(2);
        product2.setNome("Product 2");
        
        product3 = new ProductBean();
        product3.setCodice(3);
        product3.setNome("Product 3");
    }

    // ============================================================================
    // Constructor Tests
    // ============================================================================

    @Nested
    @DisplayName("Constructor Tests")
    class ConstructorTests {

        @Test
        @DisplayName("New cart is empty")
        void testNewCartIsEmpty() {
            Cart newCart = new Cart();
            assertTrue(newCart.getProducts().isEmpty());
            assertEquals(0, newCart.getCartSize());
        }
    }

    // ============================================================================
    // AddProduct Tests (Branches CART-B1)
    // ============================================================================

    @Nested
    @DisplayName("AddProduct Tests")
    class AddProductTests {

        @Test
        @DisplayName("B1-False: Add new product creates entry with quantity 1")
        void testAddNewProduct() {
            cart.addProduct(product1);
            
            assertEquals(1, cart.getProductQuantity(product1));
            assertEquals(1, cart.getProducts().size());
        }

        @Test
        @DisplayName("B1-True: Add existing product increments quantity")
        void testAddExistingProductIncrementsQuantity() {
            cart.addProduct(product1);
            cart.addProduct(product1);
            
            assertEquals(2, cart.getProductQuantity(product1));
            assertEquals(1, cart.getProducts().size());
        }

        @Test
        @DisplayName("Add same product multiple times")
        void testAddSameProductMultipleTimes() {
            cart.addProduct(product1);
            cart.addProduct(product1);
            cart.addProduct(product1);
            
            assertEquals(3, cart.getProductQuantity(product1));
        }

        @Test
        @DisplayName("Add multiple different products")
        void testAddMultipleDifferentProducts() {
            cart.addProduct(product1);
            cart.addProduct(product2);
            cart.addProduct(product3);
            
            assertEquals(1, cart.getProductQuantity(product1));
            assertEquals(1, cart.getProductQuantity(product2));
            assertEquals(1, cart.getProductQuantity(product3));
            assertEquals(3, cart.getProducts().size());
        }

        @Test
        @DisplayName("Add multiple products with mixed quantities")
        void testAddMixedQuantities() {
            cart.addProduct(product1);
            cart.addProduct(product1);
            cart.addProduct(product2);
            cart.addProduct(product1);
            cart.addProduct(product2);
            
            assertEquals(3, cart.getProductQuantity(product1));
            assertEquals(2, cart.getProductQuantity(product2));
        }
    }

    // ============================================================================
    // DeleteProduct Tests (Branches CART-B2, CART-B3)
    // ============================================================================

    @Nested
    @DisplayName("DeleteProduct Tests")
    class DeleteProductTests {

        @Test
        @DisplayName("B2-False: Delete from empty cart does nothing")
        void testDeleteFromEmptyCart() {
            cart.deleteProduct(product1);
            
            assertTrue(cart.getProducts().isEmpty());
        }

        @Test
        @DisplayName("B2-False: Delete non-existent product does nothing")
        void testDeleteNonExistentProduct() {
            cart.addProduct(product1);
            cart.deleteProduct(product2);
            
            assertEquals(1, cart.getProductQuantity(product1));
            assertEquals(1, cart.getProducts().size());
        }

        @Test
        @DisplayName("B2-True, B3-True: Delete product with quantity > 1 decrements")
        void testDeleteProductDecrementsQuantity() {
            cart.addProduct(product1);
            cart.addProduct(product1);
            cart.addProduct(product1);
            
            cart.deleteProduct(product1);
            
            assertEquals(2, cart.getProductQuantity(product1));
            assertTrue(cart.getProducts().contains(product1));
        }

        @Test
        @DisplayName("B2-True, B3-False: Delete product with quantity = 1 removes it")
        void testDeleteProductRemovesWhenQuantityOne() {
            cart.addProduct(product1);
            
            cart.deleteProduct(product1);
            
            assertEquals(0, cart.getProductQuantity(product1));
            assertFalse(cart.getProducts().contains(product1));
        }

        @Test
        @DisplayName("Delete until removed")
        void testDeleteUntilRemoved() {
            cart.addProduct(product1);
            cart.addProduct(product1);
            
            cart.deleteProduct(product1);
            assertEquals(1, cart.getProductQuantity(product1));
            
            cart.deleteProduct(product1);
            assertEquals(0, cart.getProductQuantity(product1));
            assertFalse(cart.getProducts().contains(product1));
        }

        @Test
        @DisplayName("Delete one product doesn't affect others")
        void testDeleteDoesNotAffectOthers() {
            cart.addProduct(product1);
            cart.addProduct(product2);
            
            cart.deleteProduct(product1);
            
            assertEquals(0, cart.getProductQuantity(product1));
            assertEquals(1, cart.getProductQuantity(product2));
        }
    }

    // ============================================================================
    // GetProducts Tests
    // ============================================================================

    @Nested
    @DisplayName("GetProducts Tests")
    class GetProductsTests {

        @Test
        @DisplayName("Get products from empty cart returns empty collection")
        void testGetProductsEmptyCart() {
            Collection<ProductBean> products = cart.getProducts();
            
            assertNotNull(products);
            assertTrue(products.isEmpty());
        }

        @Test
        @DisplayName("Get products returns all added products")
        void testGetProductsReturnsAll() {
            cart.addProduct(product1);
            cart.addProduct(product2);
            
            Collection<ProductBean> products = cart.getProducts();
            
            assertEquals(2, products.size());
            assertTrue(products.contains(product1));
            assertTrue(products.contains(product2));
        }

        @Test
        @DisplayName("Get products returns defensive copy")
        void testGetProductsReturnsDefensiveCopy() {
            cart.addProduct(product1);
            
            Collection<ProductBean> products = cart.getProducts();
            products.clear();
            
            // Original cart should not be affected
            assertEquals(1, cart.getProducts().size());
        }
    }

    // ============================================================================
    // ClearCart Tests
    // ============================================================================

    @Nested
    @DisplayName("ClearCart Tests")
    class ClearCartTests {

        @Test
        @DisplayName("Clear empty cart")
        void testClearEmptyCart() {
            cart.ClearCart();
            
            assertTrue(cart.getProducts().isEmpty());
            assertEquals(0, cart.getCartSize());
        }

        @Test
        @DisplayName("Clear cart with single product")
        void testClearCartSingleProduct() {
            cart.addProduct(product1);
            
            cart.ClearCart();
            
            assertTrue(cart.getProducts().isEmpty());
            assertEquals(0, cart.getCartSize());
        }

        @Test
        @DisplayName("Clear cart with multiple products")
        void testClearCartMultipleProducts() {
            cart.addProduct(product1);
            cart.addProduct(product1);
            cart.addProduct(product2);
            cart.addProduct(product3);
            
            cart.ClearCart();
            
            assertTrue(cart.getProducts().isEmpty());
            assertEquals(0, cart.getCartSize());
            assertEquals(0, cart.getProductQuantity(product1));
            assertEquals(0, cart.getProductQuantity(product2));
            assertEquals(0, cart.getProductQuantity(product3));
        }
    }

    // ============================================================================
    // GetProductQuantity Tests (Branch CART-B4)
    // ============================================================================

    @Nested
    @DisplayName("GetProductQuantity Tests")
    class GetProductQuantityTests {

        @Test
        @DisplayName("B4-False: Get quantity of non-existent product returns 0")
        void testGetQuantityNonExistentProduct() {
            assertEquals(0, cart.getProductQuantity(product1));
        }

        @Test
        @DisplayName("B4-True: Get quantity of existing product")
        void testGetQuantityExistingProduct() {
            cart.addProduct(product1);
            cart.addProduct(product1);
            
            assertEquals(2, cart.getProductQuantity(product1));
        }

        @Test
        @DisplayName("Get quantity after product removed")
        void testGetQuantityAfterRemoval() {
            cart.addProduct(product1);
            cart.deleteProduct(product1);
            
            assertEquals(0, cart.getProductQuantity(product1));
        }
    }

    // ============================================================================
    // GetProductQuantity (Collection) Tests
    // ============================================================================

    @Nested
    @DisplayName("GetProductQuantity Collection Tests")
    class GetProductQuantityCollectionTests {

        @Test
        @DisplayName("Get quantities for collection of products")
        void testGetQuantitiesForCollection() {
            cart.addProduct(product1);
            cart.addProduct(product1);
            cart.addProduct(product2);
            
            Collection<ProductBean> products = cart.getProducts();
            Map<ProductBean, Integer> quantities = cart.getProductQuantity(products);
            
            assertEquals(2, quantities.get(product1));
            assertEquals(1, quantities.get(product2));
        }

        @Test
        @DisplayName("Get quantities for empty collection")
        void testGetQuantitiesEmptyCollection() {
            Collection<ProductBean> products = cart.getProducts();
            Map<ProductBean, Integer> quantities = cart.getProductQuantity(products);
            
            assertTrue(quantities.isEmpty());
        }
    }

    // ============================================================================
    // GetProductQuantities Tests
    // ============================================================================

    @Nested
    @DisplayName("GetProductQuantities Tests")
    class GetProductQuantitiesTests {

        @Test
        @DisplayName("Get all quantities from empty cart")
        void testGetQuantitiesEmptyCart() {
            Map<ProductBean, Integer> quantities = cart.getProductQuantities();
            
            assertNotNull(quantities);
            assertTrue(quantities.isEmpty());
        }

        @Test
        @DisplayName("Get all quantities from cart with products")
        void testGetQuantitiesWithProducts() {
            cart.addProduct(product1);
            cart.addProduct(product1);
            cart.addProduct(product2);
            
            Map<ProductBean, Integer> quantities = cart.getProductQuantities();
            
            assertEquals(2, quantities.size());
            assertEquals(2, quantities.get(product1));
            assertEquals(1, quantities.get(product2));
        }
    }

    // ============================================================================
    // GetCartSize Tests
    // ============================================================================

    @Nested
    @DisplayName("GetCartSize Tests")
    class GetCartSizeTests {

        @Test
        @DisplayName("Size of empty cart is 0")
        void testSizeEmptyCart() {
            assertEquals(0, cart.getCartSize());
        }

        @Test
        @DisplayName("Size counts total quantity of items")
        void testSizeCountsTotalQuantity() {
            cart.addProduct(product1);
            cart.addProduct(product1);
            cart.addProduct(product2);
            
            assertEquals(3, cart.getCartSize());
        }

        @Test
        @DisplayName("Size updates after delete")
        void testSizeUpdatesAfterDelete() {
            cart.addProduct(product1);
            cart.addProduct(product1);
            
            assertEquals(2, cart.getCartSize());
            
            cart.deleteProduct(product1);
            
            assertEquals(1, cart.getCartSize());
        }

        @Test
        @DisplayName("Size with many products")
        void testSizeManyProducts() {
            for (int i = 0; i < 5; i++) {
                cart.addProduct(product1);
                cart.addProduct(product2);
            }
            
            assertEquals(10, cart.getCartSize());
        }
    }

    // ============================================================================
    // Loop Boundary Tests
    // ============================================================================

    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {

        @Test
        @DisplayName("Loop: 0 iterations (empty cart)")
        void testLoopZeroIterations() {
            assertEquals(0, cart.getCartSize());
            assertTrue(cart.getProducts().isEmpty());
            assertTrue(cart.getProductQuantities().isEmpty());
        }

        @Test
        @DisplayName("Loop: 1 iteration (single product with quantity 1)")
        void testLoopOneIteration() {
            cart.addProduct(product1);
            
            assertEquals(1, cart.getCartSize());
            assertEquals(1, cart.getProducts().size());
        }

        @Test
        @DisplayName("Loop: >1 iterations (multiple products)")
        void testLoopMultipleIterations() {
            cart.addProduct(product1);
            cart.addProduct(product2);
            cart.addProduct(product3);
            
            assertEquals(3, cart.getCartSize());
            assertEquals(3, cart.getProducts().size());
        }

        @Test
        @DisplayName("Loop: many iterations with quantities")
        void testLoopManyIterations() {
            for (int i = 0; i < 10; i++) {
                cart.addProduct(product1);
            }
            
            assertEquals(10, cart.getCartSize());
            assertEquals(10, cart.getProductQuantity(product1));
        }
    }

    // ============================================================================
    // Integration Scenarios
    // ============================================================================

    @Nested
    @DisplayName("Integration Scenarios")
    class IntegrationScenarios {

        @Test
        @DisplayName("Complete shopping flow: add, update, clear")
        void testCompleteShoppingFlow() {
            // Add products
            cart.addProduct(product1);
            cart.addProduct(product1);
            cart.addProduct(product2);
            
            assertEquals(3, cart.getCartSize());
            assertEquals(2, cart.getProductQuantity(product1));
            
            // Remove one item
            cart.deleteProduct(product1);
            assertEquals(2, cart.getCartSize());
            assertEquals(1, cart.getProductQuantity(product1));
            
            // Clear cart
            cart.ClearCart();
            assertEquals(0, cart.getCartSize());
        }

        @Test
        @DisplayName("Add and remove same product repeatedly")
        void testAddRemoveRepeatedly() {
            cart.addProduct(product1);
            assertEquals(1, cart.getProductQuantity(product1));
            
            cart.deleteProduct(product1);
            assertEquals(0, cart.getProductQuantity(product1));
            
            cart.addProduct(product1);
            assertEquals(1, cart.getProductQuantity(product1));
            
            cart.addProduct(product1);
            assertEquals(2, cart.getProductQuantity(product1));
        }
    }
}
