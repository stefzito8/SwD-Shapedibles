package integration;

import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Statement;

import javax.sql.DataSource;

import org.h2.jdbcx.JdbcDataSource;

/**
 * H2 Test Database Configuration for Integration Tests.
 * 
 * <h2>Purpose</h2>
 * <p>Provides an in-memory H2 database that replaces the SQLite production database
 * for integration testing purposes.</p>
 * 
 * <h2>Integration Strategy: Modified Sandwich</h2>
 * <p>Per SPEC.md: "Modified Sandwich approach is recommended because:
 * <ul>
 *   <li>All components should be unit tested first (satisfying unit testing requirements)</li>
 *   <li>Middle-layer components (controllers) integrate with both model (lower) and filters/web layer (upper)</li>
 *   <li>This minimizes the need for extensive stubs/drivers</li>
 * </ul>
 * </p>
 * 
 * <h2>Database Schema</h2>
 * <p>The H2 test database mirrors the SQLite production schema with tables:</p>
 * <ul>
 *   <li>products - Product catalog</li>
 *   <li>info - Product information (description, cost, availability)</li>
 *   <li>nutrition_table - Nutritional information</li>
 *   <li>images - Product images</li>
 *   <li>users - User accounts</li>
 *   <li>addresses - User addresses</li>
 *   <li>orders - Order records</li>
 *   <li>contain - Order items (cart/order relationship)</li>
 * </ul>
 * 
 * <h2>Usage</h2>
 * <pre>
 * {@code
 * @BeforeEach
 * void setUp() {
 *     H2TestDatabase.initializeDatabase();
 *     DataSource ds = H2TestDatabase.getDataSource();
 *     // Use ds for DAO testing
 * }
 * 
 * @AfterEach
 * void tearDown() {
 *     H2TestDatabase.resetDatabase();
 * }
 * }
 * </pre>
 * 
 * @see DatabaseIntegrationTest
 * @see ControllerModelIntegrationTest
 */
public class H2TestDatabase {
    
    private static final String DB_URL = "jdbc:h2:mem:testdb;DB_CLOSE_DELAY=-1;MODE=MySQL";
    private static final String DB_USER = "sa";
    private static final String DB_PASSWORD = "";
    
    private static JdbcDataSource dataSource;
    private static boolean initialized = false;
    
    /**
     * Gets the H2 DataSource instance.
     * Creates a new DataSource if one doesn't exist.
     * 
     * @return DataSource configured for H2 in-memory database
     */
    public static synchronized DataSource getDataSource() {
        if (dataSource == null) {
            dataSource = new JdbcDataSource();
            dataSource.setURL(DB_URL);
            dataSource.setUser(DB_USER);
            dataSource.setPassword(DB_PASSWORD);
        }
        return dataSource;
    }
    
    /**
     * Initializes the database schema.
     * Creates all tables if they don't exist.
     * This method is idempotent - safe to call multiple times.
     * 
     * @throws RuntimeException if database initialization fails
     */
    public static synchronized void initializeDatabase() {
        if (initialized) {
            return;
        }
        
        try (Connection conn = getDataSource().getConnection();
             Statement stmt = conn.createStatement()) {
            
            // Create schema
            createSchema(stmt);
            initialized = true;
            
        } catch (SQLException e) {
            throw new RuntimeException("Failed to initialize H2 test database", e);
        }
    }
    
    /**
     * Initializes the database with test data.
     * Creates schema and populates with sample data for testing.
     * 
     * @throws RuntimeException if database initialization fails
     */
    public static synchronized void initializeDatabaseWithTestData() {
        try (Connection conn = getDataSource().getConnection();
             Statement stmt = conn.createStatement()) {
            
            // Create schema
            createSchema(stmt);
            
            // Insert test data
            insertTestData(stmt);
            
            initialized = true;
            
        } catch (SQLException e) {
            throw new RuntimeException("Failed to initialize H2 test database with test data", e);
        }
    }
    
    /**
     * Resets the database to a clean state.
     * Drops all tables and recreates the schema.
     * Use this between tests to ensure isolation.
     */
public static synchronized void resetDatabase() {
    try (Connection conn = getDataSource().getConnection();
         Statement stmt = conn.createStatement()) {
        
        // Drop all tables in reverse order (respect foreign keys)
        stmt.execute("DROP TABLE IF EXISTS Contains");
        stmt.execute("DROP TABLE IF EXISTS orders");
        stmt.execute("DROP TABLE IF EXISTS adresses");
        stmt.execute("DROP TABLE IF EXISTS images");
        stmt.execute("DROP TABLE IF EXISTS nutritionalValues");
        stmt.execute("DROP TABLE IF EXISTS product_info");
        stmt.execute("DROP TABLE IF EXISTS product");
        stmt.execute("DROP TABLE IF EXISTS users");
        
        // Recreate schema so tables exist for tests
        createSchema(stmt);
        initialized = true;
        
    } catch (SQLException e) {
        throw new RuntimeException("Failed to reset H2 test database", e);
    }
}
    
    /**
     * Clears all data from tables but keeps the schema.
     * Faster than resetDatabase() when schema doesn't need recreation.
     */
    public static synchronized void clearAllData() {
        try (Connection conn = getDataSource().getConnection();
             Statement stmt = conn.createStatement()) {
            
            // Disable referential integrity temporarily
            stmt.execute("SET REFERENTIAL_INTEGRITY FALSE");
            
            // Truncate all tables
            stmt.execute("TRUNCATE TABLE Contains");
            stmt.execute("TRUNCATE TABLE orders");
            stmt.execute("TRUNCATE TABLE adresses");
            stmt.execute("TRUNCATE TABLE users");
            stmt.execute("TRUNCATE TABLE images");
            stmt.execute("TRUNCATE TABLE nutritionalValues");
            stmt.execute("TRUNCATE TABLE product_info");
            stmt.execute("TRUNCATE TABLE product");
            
            // Re-enable referential integrity
            stmt.execute("SET REFERENTIAL_INTEGRITY TRUE");
            
        } catch (SQLException e) {
            throw new RuntimeException("Failed to clear H2 test database data", e);
        }
    }
    
    /**
     * Gets a new connection to the test database.
     * 
     * @return a new Connection instance
     * @throws SQLException if connection fails
     */
    public static Connection getConnection() throws SQLException {
        return getDataSource().getConnection();
    }
    
    /**
     * Checks if the database has been initialized.
     * 
     * @return true if initializeDatabase() has been called successfully
     */
    public static boolean isInitialized() {
        return initialized;
    }
    
    private static void createSchema(Statement stmt) throws SQLException {
        // Users table (must be created first - referenced by others)
        stmt.execute("""
            CREATE TABLE IF NOT EXISTS users (
                USERNAME VARCHAR(50) PRIMARY KEY,
                EMAIL VARCHAR(100) NOT NULL UNIQUE,
                PASS VARCHAR(255) NOT NULL,
                NAME_SURNAME VARCHAR(100),
                GENDER VARCHAR(10),
                COUNTRY VARCHAR(50),
                BIRTHDAY DATE,
                USER_ADMIN INT DEFAULT 0
            )
            """);
        
        // Products table
        // CURRENT_INFO is an alias for CURRENT_INFOS to support both naming conventions
        stmt.execute("""
            CREATE TABLE IF NOT EXISTS product (
                CODE INT PRIMARY KEY AUTO_INCREMENT,
                NAME VARCHAR(100) NOT NULL,
                CURRENT_INFOS INT,
                CURRENT_INFO INT AS (CURRENT_INFOS)
            )
            """);
        
        // Product info table
        stmt.execute("""
            CREATE TABLE IF NOT EXISTS product_info (
                CODE INT PRIMARY KEY AUTO_INCREMENT,
                NAME VARCHAR(100) NOT NULL,
                PRICE DECIMAL(10,2) NOT NULL,
                DESCRIPTION VARCHAR(500),
                AVAILABILITY INT NOT NULL DEFAULT 0,
                TYPE VARCHAR(50)
            )
            """);
        
        // Nutrition table
        stmt.execute("""
            CREATE TABLE IF NOT EXISTS nutritionalValues (
                PRODUCT_CODE INT PRIMARY KEY,
                ENERGY DECIMAL(10,2),
                FATS DECIMAL(10,2),
                SATURATED_FATS DECIMAL(10,2),
                CARBS DECIMAL(10,2),
                SUGARS DECIMAL(10,2),
                FIBERS DECIMAL(10,2),
                PROTEINS DECIMAL(10,2),
                SALT DECIMAL(10,2)
            )
            """);
        
        // Images table
        stmt.execute("""
            CREATE TABLE IF NOT EXISTS images (
                Images_Num INT PRIMARY KEY AUTO_INCREMENT,
                Product_Code INT NOT NULL,
                img VARCHAR(255) NOT NULL
            )
            """);
        
        // Addresses table (note: typo in table name is intentional - matches DAO)
        // FK constraints removed for test isolation - allows inserting test data without parent records
        stmt.execute("""
            CREATE TABLE IF NOT EXISTS adresses (
                ID VARCHAR(50) PRIMARY KEY,
                "user" VARCHAR(50) NOT NULL,
                country VARCHAR(50),
                street VARCHAR(200) NOT NULL,
                city VARCHAR(100),
                number VARCHAR(20),
                Postal_Code VARCHAR(20)
            )
            """);
        
        // Orders table
        // address is VARCHAR to match DAO behavior (stores address string, not FK)
        stmt.execute("""
            CREATE TABLE IF NOT EXISTS orders (
                code INT PRIMARY KEY AUTO_INCREMENT,
                "User" VARCHAR(50) NOT NULL,
                address VARCHAR(255),
                state VARCHAR(50) DEFAULT 'PENDING',
                order_date VARCHAR(50),
                total_cost DECIMAL(10,2)
            )
            """);
        
        // Contains table (order items)
        // FK constraints removed for test isolation
        stmt.execute("""
            CREATE TABLE IF NOT EXISTS Contains (
                order_code INT NOT NULL,
                info_code INT NOT NULL,
                Quantity INT NOT NULL DEFAULT 1,
                PRIMARY KEY (order_code, info_code)
            )
            """);
    }
    
    private static void insertTestData(Statement stmt) throws SQLException {
        // Sample users (password hash for 'password123')
        stmt.execute("""
            INSERT INTO users (USERNAME, EMAIL, PASS, NAME_SURNAME, GENDER, COUNTRY, BIRTHDAY, USER_ADMIN) 
            VALUES ('testuser', 'testuser@example.com', '5e884898da28047d91684a56a44e8acb', 'Test User', 'M', 'Italy', '1990-01-15', 0)
            """);
        stmt.execute("""
            INSERT INTO users (USERNAME, EMAIL, PASS, NAME_SURNAME, GENDER, COUNTRY, BIRTHDAY, USER_ADMIN) 
            VALUES ('adminuser', 'admin@example.com', '5e884898da28047d91684a56a44e8acb', 'Admin User', 'M', 'Italy', '1985-06-20', 1)
            """);
        
        // Sample products
        stmt.execute("INSERT INTO product (CODE, NAME, CURRENT_INFOS) VALUES (1, 'Protein Shake Vanilla', 1)");
        stmt.execute("INSERT INTO product (CODE, NAME, CURRENT_INFOS) VALUES (2, 'Protein Shake Chocolate', 2)");
        stmt.execute("INSERT INTO product (CODE, NAME, CURRENT_INFOS) VALUES (3, 'Energy Bar', 3)");
        stmt.execute("INSERT INTO product (CODE, NAME, CURRENT_INFOS) VALUES (4, 'Pre-Workout Mix', 4)");
        stmt.execute("INSERT INTO product (CODE, NAME, CURRENT_INFOS) VALUES (5, 'BCAA Capsules', 5)");
        
        // Sample product info
        stmt.execute("""
            INSERT INTO product_info (CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE) 
            VALUES (1, 'Protein Shake Vanilla', 29.99, 'Delicious vanilla flavored protein shake with 25g protein per serving', 100, 'Protein')
            """);
        stmt.execute("""
            INSERT INTO product_info (CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE) 
            VALUES (2, 'Protein Shake Chocolate', 29.99, 'Rich chocolate protein shake with 25g protein per serving', 50, 'Protein')
            """);
        stmt.execute("""
            INSERT INTO product_info (CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE) 
            VALUES (3, 'Energy Bar', 3.99, 'High protein energy bar for on-the-go nutrition', 200, 'Snack')
            """);
        stmt.execute("""
            INSERT INTO product_info (CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE) 
            VALUES (4, 'Pre-Workout Mix', 39.99, 'Pre-workout formula for enhanced performance', 75, 'Supplement')
            """);
        stmt.execute("""
            INSERT INTO product_info (CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE) 
            VALUES (5, 'BCAA Capsules', 24.99, 'BCAA capsules for muscle recovery', 150, 'Supplement')
            """);
        
        // Sample nutrition data
        stmt.execute("""
            INSERT INTO nutritionalValues (PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT) 
            VALUES (1, 120.0, 2.0, 0.5, 5.0, 2.0, 1.0, 25.0, 0.3)
            """);
        stmt.execute("""
            INSERT INTO nutritionalValues (PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT) 
            VALUES (2, 130.0, 2.5, 0.8, 6.0, 3.0, 1.5, 25.0, 0.35)
            """);
        stmt.execute("""
            INSERT INTO nutritionalValues (PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT) 
            VALUES (3, 200.0, 8.0, 3.0, 25.0, 10.0, 3.0, 15.0, 0.2)
            """);
        stmt.execute("""
            INSERT INTO nutritionalValues (PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT) 
            VALUES (4, 150.0, 1.0, 0.2, 20.0, 5.0, 0.5, 5.0, 0.8)
            """);
        stmt.execute("""
            INSERT INTO nutritionalValues (PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT) 
            VALUES (5, 50.0, 0.5, 0.1, 2.0, 0.5, 0.0, 10.0, 0.1)
            """);
        
        // Sample images
        stmt.execute("INSERT INTO images (Images_Num, Product_Code, img) VALUES (1, 1, 'vanilla_shake.png')");
        stmt.execute("INSERT INTO images (Images_Num, Product_Code, img) VALUES (2, 2, 'chocolate_shake.png')");
        
        // Sample addresses
        stmt.execute("""
            INSERT INTO adresses (ID, "user", country, street, city, number, Postal_Code) 
            VALUES (1, 'testuser', 'Italy', 'Via Roma', 'Milano', '123', '20100')
            """);
        
        // Sample orders
        stmt.execute("""
            INSERT INTO orders (code, "User", address, state, order_date, total_cost) 
            VALUES (1, 'testuser', 1, 'COMPLETED', '2024-01-15 10:30:00', 59.98)
            """);
        
        // Sample order items
        stmt.execute("""
            INSERT INTO Contains (order_code, info_code, Quantity) 
            VALUES (1, 1, 2)
            """);
    }
}
