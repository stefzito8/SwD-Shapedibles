package benchmark;

import model.bean.ImageBean;
import model.bean.InfoBean;
import model.bean.ProductBean;
import model.datasource.ImageDaoDataSource;
import model.datasource.InfoDaoDataSource;
import model.datasource.ProductDaoDataSource;
import org.h2.jdbcx.JdbcDataSource;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * JMH Microbenchmarks for Data Access Layer operations.
 * 
 * <p>The DataSource layer is performance-critical because:</p>
 * <ul>
 *   <li>Database operations are I/O-bound</li>
 *   <li>Connection acquisition/release overhead</li>
 *   <li>Query compilation and execution</li>
 *   <li>Result set processing and object mapping</li>
 *   <li>N+1 query patterns in doRetrieveByKey (calls ImageDaoDataSource)</li>
 * </ul>
 * 
 * <p>Uses H2 in-memory database for consistent, fast benchmarking.</p>
 */
@BenchmarkMode({Mode.AverageTime, Mode.Throughput})
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@State(Scope.Thread)
@Warmup(iterations = 3, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 2, jvmArgs = {"-Xms256M", "-Xmx256M"})
public class DataSourceBenchmark {

    private DataSource dataSource;
    private ProductDaoDataSource productDao;
    private InfoDaoDataSource infoDao;
    private ImageDaoDataSource imageDao;
    
    // Test data
    private static final int TEST_PRODUCT_ID = 1;
    private static final String TEST_SEARCH_QUERY = "Protein";
    
    @Param({"10", "50", "100"})
    private int dataSize;

    @Setup(Level.Trial)
    public void setUp() throws SQLException {
        // Create H2 in-memory database
        JdbcDataSource h2DataSource = new JdbcDataSource();
        h2DataSource.setURL("jdbc:h2:mem:benchmark;DB_CLOSE_DELAY=-1");
        h2DataSource.setUser("sa");
        h2DataSource.setPassword("");
        
        dataSource = h2DataSource;
        
        // Initialize DAOs
        productDao = new ProductDaoDataSource(dataSource);
        infoDao = new InfoDaoDataSource(dataSource);
        imageDao = new ImageDaoDataSource(dataSource);
        
        // Create schema
        createSchema();
        
        // Populate test data
        populateTestData();
    }

    private void createSchema() throws SQLException {
        try (Connection conn = dataSource.getConnection();
             Statement stmt = conn.createStatement()) {
            
            // Product table
            stmt.execute("""
                CREATE TABLE IF NOT EXISTS product (
                    CODE INT PRIMARY KEY AUTO_INCREMENT,
                    CURRENT_INFOS INT,
                    NAME VARCHAR(255)
                )
            """);
            
            // Product info table
            stmt.execute("""
                CREATE TABLE IF NOT EXISTS product_info (
                    CODE INT PRIMARY KEY AUTO_INCREMENT,
                    NAME VARCHAR(255),
                    PRICE DECIMAL(10,2),
                    DESCRIPTION TEXT,
                    AVAILABILITY INT,
                    TYPE VARCHAR(50)
                )
            """);
            
            // Images table
            stmt.execute("""
                CREATE TABLE IF NOT EXISTS images (
                    Images_Num INT,
                    Product_Code INT,
                    img VARCHAR(255),
                    PRIMARY KEY (Images_Num, Product_Code)
                )
            """);
        }
    }

    private void populateTestData() throws SQLException {
        try (Connection conn = dataSource.getConnection();
             Statement stmt = conn.createStatement()) {
            
            // Clear existing data
            stmt.execute("DELETE FROM images");
            stmt.execute("DELETE FROM product_info");
            stmt.execute("DELETE FROM product");
            
            // Reset auto-increment
            stmt.execute("ALTER TABLE product ALTER COLUMN CODE RESTART WITH 1");
            stmt.execute("ALTER TABLE product_info ALTER COLUMN CODE RESTART WITH 1");
            
            // Insert products
            for (int i = 1; i <= dataSize; i++) {
                String name = i % 3 == 0 ? "Protein Powder " + i : "Product " + i;
                stmt.execute(String.format(
                    "INSERT INTO product (CURRENT_INFOS, NAME) VALUES (%d, '%s')",
                    i, name
                ));
                
                // Insert corresponding info
                stmt.execute(String.format(
                    "INSERT INTO product_info (NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE) VALUES ('%s', %.2f, 'Description for %s', %d, 'Type%d')",
                    name, 19.99 + i, name, i % 2, i % 5
                ));
                
                // Insert 2 images per product
                for (int j = 1; j <= 2; j++) {
                    stmt.execute(String.format(
                        "INSERT INTO images (Images_Num, Product_Code, img) VALUES (%d, %d, 'product_%d_img%d.jpg')",
                        j, i, i, j
                    ));
                }
            }
        }
    }

    @TearDown(Level.Trial)
    public void tearDown() throws SQLException {
        try (Connection conn = dataSource.getConnection();
             Statement stmt = conn.createStatement()) {
            stmt.execute("DROP TABLE IF EXISTS images");
            stmt.execute("DROP TABLE IF EXISTS product_info");
            stmt.execute("DROP TABLE IF EXISTS product");
        }
    }

    // ==================== PRODUCT DAO BENCHMARKS ====================

    /**
     * Benchmark: Retrieve single product by key.
     * Tests primary key lookup with additional image fetch (N+1 pattern).
     */
    @Benchmark
    public void productDoRetrieveByKey(Blackhole bh) throws SQLException {
        ProductBean product = productDao.doRetrieveByKey(TEST_PRODUCT_ID);
        bh.consume(product);
    }

    /**
     * Benchmark: Retrieve product by name.
     * Tests string comparison in WHERE clause.
     */
    @Benchmark
    public void productDoRetrieveByName(Blackhole bh) throws SQLException {
        ProductBean product = productDao.doRetrieveByName("Protein Powder 3");
        bh.consume(product);
    }

    /**
     * Benchmark: Retrieve all products (no ordering).
     * Tests bulk retrieval with image loading for each product.
     */
    @Benchmark
    public void productDoRetrieveAll(Blackhole bh) throws SQLException {
        Collection<ProductBean> products = productDao.doRetrieveAll(null);
        bh.consume(products);
    }

    /**
     * Benchmark: Retrieve all products with ordering.
     * Tests ORDER BY clause overhead.
     */
    @Benchmark
    public void productDoRetrieveAllOrdered(Blackhole bh) throws SQLException {
        Collection<ProductBean> products = productDao.doRetrieveAll("NAME");
        bh.consume(products);
    }

    /**
     * Benchmark: Search products by name pattern.
     * Tests LIKE query with wildcards.
     */
    @Benchmark
    public void productSearchByName(Blackhole bh) throws SQLException {
        List<ProductBean> products = productDao.searchByName(TEST_SEARCH_QUERY);
        bh.consume(products);
    }

    /**
     * Benchmark: Save new product.
     * Tests INSERT operation.
     */
    @Benchmark
    public void productDoSave(Blackhole bh) throws SQLException {
        ProductBean newProduct = new ProductBean();
        newProduct.setNome("Benchmark Product");
        newProduct.setInfoCorrenti(1);
        productDao.doSave(newProduct);
        bh.consume(newProduct);
    }

    /**
     * Benchmark: Delete product.
     * Tests DELETE operation.
     */
    @Benchmark
    public void productDoDelete(Blackhole bh) throws SQLException {
        // First insert a product to delete
        ProductBean toDelete = new ProductBean();
        toDelete.setNome("ToDelete");
        toDelete.setInfoCorrenti(1);
        productDao.doSave(toDelete);
        
        boolean deleted = productDao.doDelete(dataSize + 1);
        bh.consume(deleted);
    }

    /**
     * Benchmark: Update product info.
     * Tests UPDATE operation.
     */
    @Benchmark
    public void productDoUpdateInfo(Blackhole bh) throws SQLException {
        productDao.doUpdateInfo(TEST_PRODUCT_ID, 999);
        bh.consume(true);
    }

    // ==================== INFO DAO BENCHMARKS ====================

    /**
     * Benchmark: Retrieve info by key.
     * Tests simple primary key lookup.
     */
    @Benchmark
    public void infoDoRetrieveByKey(Blackhole bh) throws SQLException {
        InfoBean info = infoDao.doRetrieveByKey(TEST_PRODUCT_ID);
        bh.consume(info);
    }

    /**
     * Benchmark: Retrieve info by name.
     * Tests string comparison lookup.
     */
    @Benchmark
    public void infoDoRetrieveByName(Blackhole bh) throws SQLException {
        InfoBean info = infoDao.doRetrieveByName("Protein Powder 3");
        bh.consume(info);
    }

    /**
     * Benchmark: Save new info.
     * Tests INSERT with multiple fields.
     */
    @Benchmark
    public void infoDoSave(Blackhole bh) throws SQLException {
        InfoBean newInfo = new InfoBean();
        newInfo.setNome("Benchmark Info");
        newInfo.setCosto(29.99);
        newInfo.setDescrizione("Benchmark description");
        newInfo.setDisponibilità(1);
        newInfo.setTipologia("BenchmarkType");
        infoDao.doSave(newInfo);
        bh.consume(newInfo);
    }

    // ==================== IMAGE DAO BENCHMARKS ====================

    /**
     * Benchmark: Retrieve all images for a product.
     * Tests foreign key lookup pattern.
     */
    @Benchmark
    public void imageDoRetrieveByProduct(Blackhole bh) throws SQLException {
        Collection<ImageBean> images = imageDao.doRetrieveByProduct(TEST_PRODUCT_ID);
        bh.consume(images);
    }

    /**
     * Benchmark: Retrieve all images.
     * Tests bulk image retrieval.
     */
    @Benchmark
    public void imageDoRetrieveAll(Blackhole bh) throws SQLException {
        Collection<ImageBean> images = imageDao.doRetrieveAll(null);
        bh.consume(images);
    }

    // ==================== CONNECTION BENCHMARKS ====================

    /**
     * Benchmark: Connection acquisition from DataSource.
     * Tests connection pool performance.
     */
    @Benchmark
    public void connectionAcquisition(Blackhole bh) throws SQLException {
        try (Connection conn = dataSource.getConnection()) {
            bh.consume(conn);
        }
    }

    /**
     * Benchmark: Prepared statement creation.
     * Tests statement compilation overhead.
     */
    @Benchmark
    public void preparedStatementCreation(Blackhole bh) throws SQLException {
        try (Connection conn = dataSource.getConnection();
             java.sql.PreparedStatement ps = conn.prepareStatement("SELECT * FROM product WHERE CODE = ?")) {
            bh.consume(ps);
        }
    }

    /**
     * Main method to run benchmarks standalone.
     */
    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(DataSourceBenchmark.class.getSimpleName())
                .forks(1)
                .warmupIterations(2)
                .measurementIterations(3)
                .build();

        new Runner(opt).run();
    }
}
