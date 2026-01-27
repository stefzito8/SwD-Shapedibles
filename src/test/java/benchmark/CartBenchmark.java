package benchmark;

import model.Cart;
import model.bean.ProductBean;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.concurrent.TimeUnit;

/**
 * JMH Microbenchmarks for Cart operations.
 * 
 * <p>The Cart class is one of the most performance-critical components because:</p>
 * <ul>
 *   <li>Used in every shopping session</li>
 *   <li>High frequency of add/delete operations</li>
 *   <li>HashMap operations with ProductBean keys (hashCode/equals overhead)</li>
 *   <li>Stream operations in getCartSize() called frequently for UI updates</li>
 * </ul>
 * 
 * <p>These benchmarks test:</p>
 * <ul>
 *   <li>Add product performance (HashMap put with collision handling)</li>
 *   <li>Delete product performance (get + conditional remove)</li>
 *   <li>Cart size calculation (stream reduction)</li>
 *   <li>Bulk operations (getProductQuantities)</li>
 * </ul>
 */
@BenchmarkMode({Mode.AverageTime, Mode.Throughput})
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Thread)
@Warmup(iterations = 3, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 2, jvmArgs = {"-Xms256M", "-Xmx256M"})
public class CartBenchmark {

    private Cart cart;
    private Cart prefilledCart;
    private ProductBean singleProduct;
    private List<ProductBean> productList;
    
    // Different cart sizes for scalability testing
    @Param({"10", "50", "100"})
    private int cartSize;

    @Setup(Level.Trial)
    public void setupTrial() {
        // Create product list for benchmarks
        productList = new ArrayList<>();
        for (int i = 0; i < 200; i++) {
            ProductBean product = new ProductBean();
            product.setCodice(i);
            product.setNome("Product " + i);
            product.setInfoCorrenti(i * 10);
            productList.add(product);
        }
        
        // Single product for isolated tests
        singleProduct = new ProductBean();
        singleProduct.setCodice(999);
        singleProduct.setNome("Test Product");
        singleProduct.setInfoCorrenti(100);
    }

    @Setup(Level.Invocation)
    public void setupInvocation() {
        // Fresh cart for each invocation
        cart = new Cart();
        
        // Pre-filled cart for tests requiring existing items
        prefilledCart = new Cart();
        for (int i = 0; i < cartSize; i++) {
            prefilledCart.addProduct(productList.get(i));
        }
    }

    // ==================== ADD OPERATIONS ====================

    /**
     * Benchmark: Adding a single product to an empty cart.
     * Tests HashMap.put with no collisions.
     */
    @Benchmark
    public void addProductToEmptyCart(Blackhole bh) {
        cart.addProduct(singleProduct);
        bh.consume(cart);
    }

    /**
     * Benchmark: Adding a product that already exists (quantity increment).
     * Tests HashMap.getOrDefault + put overhead.
     */
    @Benchmark
    public void addExistingProduct(Blackhole bh) {
        prefilledCart.addProduct(productList.get(0));
        bh.consume(prefilledCart);
    }

    /**
     * Benchmark: Adding multiple products sequentially.
     * Tests HashMap growth and rehashing behavior.
     */
    @Benchmark
    public void addMultipleProducts(Blackhole bh) {
        for (int i = 0; i < 10; i++) {
            cart.addProduct(productList.get(i));
        }
        bh.consume(cart);
    }

    // ==================== DELETE OPERATIONS ====================

    /**
     * Benchmark: Deleting a product from cart (decrement quantity).
     * Tests containsKey + get + conditional put/remove.
     */
    @Benchmark
    public void deleteProductDecrementQuantity(Blackhole bh) {
        // Add twice so delete only decrements
        prefilledCart.addProduct(productList.get(0));
        prefilledCart.deleteProduct(productList.get(0));
        bh.consume(prefilledCart);
    }

    /**
     * Benchmark: Deleting product completely (quantity becomes 0).
     * Tests HashMap.remove operation.
     */
    @Benchmark
    public void deleteProductCompletely(Blackhole bh) {
        prefilledCart.deleteProduct(productList.get(0));
        bh.consume(prefilledCart);
    }

    /**
     * Benchmark: Deleting non-existent product (no-op).
     * Tests containsKey for missing key.
     */
    @Benchmark
    public void deleteNonExistentProduct(Blackhole bh) {
        prefilledCart.deleteProduct(singleProduct);
        bh.consume(prefilledCart);
    }

    // ==================== QUERY OPERATIONS ====================

    /**
     * Benchmark: Get cart size (stream reduction).
     * This is called frequently for UI updates (cart badge count).
     * Tests stream().mapToInt().sum() performance.
     */
    @Benchmark
    public void getCartSize(Blackhole bh) {
        int size = prefilledCart.getCartSize();
        bh.consume(size);
    }

    /**
     * Benchmark: Get all products (keySet copy).
     * Tests ArrayList construction from keySet.
     */
    @Benchmark
    public void getProducts(Blackhole bh) {
        Collection<ProductBean> products = prefilledCart.getProducts();
        bh.consume(products);
    }

    /**
     * Benchmark: Get single product quantity.
     * Tests HashMap.getOrDefault performance.
     */
    @Benchmark
    public void getProductQuantity(Blackhole bh) {
        int quantity = prefilledCart.getProductQuantity(productList.get(0));
        bh.consume(quantity);
    }

    /**
     * Benchmark: Get all product quantities (bulk operation).
     * Tests iteration over keySet with multiple getOrDefault calls.
     */
    @Benchmark
    public void getProductQuantities(Blackhole bh) {
        Map<ProductBean, Integer> quantities = prefilledCart.getProductQuantities();
        bh.consume(quantities);
    }

    // ==================== CLEAR OPERATIONS ====================

    /**
     * Benchmark: Clear entire cart.
     * Tests HashMap.clear() performance based on cart size.
     */
    @Benchmark
    public void clearCart(Blackhole bh) {
        prefilledCart.ClearCart();
        bh.consume(prefilledCart);
    }

    // ==================== COMPOUND OPERATIONS ====================

    /**
     * Benchmark: Typical user session - add, modify, query cycle.
     * Simulates realistic usage pattern.
     */
    @Benchmark
    public void typicalUserSession(Blackhole bh) {
        // Add several products
        for (int i = 0; i < 5; i++) {
            cart.addProduct(productList.get(i));
        }
        
        // Increment one product
        cart.addProduct(productList.get(0));
        cart.addProduct(productList.get(0));
        
        // Remove one product
        cart.deleteProduct(productList.get(2));
        
        // Query cart state
        int size = cart.getCartSize();
        Collection<ProductBean> products = cart.getProducts();
        
        bh.consume(size);
        bh.consume(products);
    }

    /**
     * Benchmark: Hash code computation for ProductBean.
     * Critical for HashMap performance - tests Objects.hash overhead.
     */
    @Benchmark
    public void productBeanHashCode(Blackhole bh) {
        int hash = singleProduct.hashCode();
        bh.consume(hash);
    }

    /**
     * Benchmark: Equals comparison for ProductBean.
     * Called during HashMap collision resolution.
     */
    @Benchmark
    public void productBeanEquals(Blackhole bh) {
        boolean equals = singleProduct.equals(productList.get(0));
        bh.consume(equals);
    }

    /**
     * Main method to run benchmarks standalone.
     */
    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(CartBenchmark.class.getSimpleName())
                .forks(1)
                .warmupIterations(2)
                .measurementIterations(3)
                .build();

        new Runner(opt).run();
    }
}
