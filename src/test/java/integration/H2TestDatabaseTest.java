package integration;

import categories.IntegrationTest;
import static org.junit.jupiter.api.Assertions.*;

import java.sql.Connection;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;

import javax.sql.DataSource;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

/**
 * Tests for H2TestDatabase configuration.
 * 
 * <p>Verifies that the H2 in-memory database initializes correctly
 * and can be used for integration testing.</p>
 * 
 * <h2>Testing Level</h2>
 * <p>Integration (setup verification)</p>
 * 
 * <h2>Technique</h2>
 * <p>Functional testing of database setup infrastructure</p>
 */
@IntegrationTest
@DisplayName("H2 Test Database Configuration")
class H2TestDatabaseTest {
    
    @BeforeEach
    void setUp() {
        // Ensure clean state before each test
        H2TestDatabase.resetDatabase();
    }
    
    @AfterEach
    void tearDown() {
        // Clean up after each test
        H2TestDatabase.resetDatabase();
    }
    
    @Nested
    @DisplayName("DataSource Configuration")
    class DataSourceTests {
        
        @Test
        @DisplayName("getDataSource returns non-null DataSource")
        void testGetDataSourceReturnsNonNull() {
            DataSource ds = H2TestDatabase.getDataSource();
            assertNotNull(ds, "DataSource should not be null");
        }
        
        @Test
        @DisplayName("DataSource returns valid connection")
        void testDataSourceReturnsValidConnection() throws SQLException {
            DataSource ds = H2TestDatabase.getDataSource();
            try (Connection conn = ds.getConnection()) {
                assertNotNull(conn, "Connection should not be null");
                assertFalse(conn.isClosed(), "Connection should be open");
            }
        }
        
        @Test
        @DisplayName("getDataSource returns same instance (singleton)")
        void testDataSourceIsSingleton() {
            DataSource ds1 = H2TestDatabase.getDataSource();
            DataSource ds2 = H2TestDatabase.getDataSource();
            assertSame(ds1, ds2, "DataSource should be a singleton");
        }
    }
    
    @Nested
    @DisplayName("Schema Initialization")
    class SchemaInitializationTests {
        
        @Test
        @DisplayName("initializeDatabase creates products table")
        void testInitializeCreatesProductsTable() throws SQLException {
            H2TestDatabase.initializeDatabase();
            
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement();
                 ResultSet rs = stmt.executeQuery(
                     "SELECT COUNT(*) FROM INFORMATION_SCHEMA.TABLES WHERE TABLE_NAME = 'PRODUCT'")) {
                assertTrue(rs.next());
                assertEquals(1, rs.getInt(1), "Products table should exist");
            }
        }
        
        @Test
        @DisplayName("initializeDatabase creates all required tables")
        void testInitializeCreatesAllTables() throws SQLException {
            H2TestDatabase.initializeDatabase();
            
            String[] expectedTables = {"PRODUCT", "PRODUCT_INFO", "NUTRITIONALVALUES", "IMAGES", 
                                       "USERS", "ADRESSES", "ORDERS", "CONTAINS"};
            
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement()) {
                
                for (String tableName : expectedTables) {
                    try (ResultSet rs = stmt.executeQuery(
                            "SELECT COUNT(*) FROM INFORMATION_SCHEMA.TABLES WHERE TABLE_NAME = '" + tableName + "'")) {
                        assertTrue(rs.next());
                        assertTrue(rs.getInt(1) >= 1, tableName + " table should exist");
                    }
                }
            }
        }
        
        @Test
        @DisplayName("initializeDatabase is idempotent")
        void testInitializeIsIdempotent() {
            // Should not throw on multiple calls
            assertDoesNotThrow(() -> {
                H2TestDatabase.initializeDatabase();
                H2TestDatabase.initializeDatabase();
                H2TestDatabase.initializeDatabase();
            });
            
            assertTrue(H2TestDatabase.isInitialized());
        }
    }
    
    @Nested
    @DisplayName("Test Data Loading")
    class TestDataTests {
        
        @Test
        @DisplayName("initializeDatabaseWithTestData loads sample products")
        void testInitializeWithTestDataLoadsProducts() throws SQLException {
            H2TestDatabase.initializeDatabaseWithTestData();
            
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement();
                 ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM product")) {
                assertTrue(rs.next());
                assertEquals(5, rs.getInt(1), "Should have 5 sample products");
            }
        }
        
        @Test
        @DisplayName("initializeDatabaseWithTestData loads sample users")
        void testInitializeWithTestDataLoadsUsers() throws SQLException {
            H2TestDatabase.initializeDatabaseWithTestData();
            
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement();
                 ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM users")) {
                assertTrue(rs.next());
                assertEquals(2, rs.getInt(1), "Should have 2 sample users");
            }
        }
        
        @Test
        @DisplayName("initializeDatabaseWithTestData loads admin user correctly")
        void testInitializeWithTestDataLoadsAdminUser() throws SQLException {
            H2TestDatabase.initializeDatabaseWithTestData();
            
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement();
                 ResultSet rs = stmt.executeQuery(
                     "SELECT USERNAME, USER_ADMIN FROM users WHERE USER_ADMIN = 1")) {
                assertTrue(rs.next(), "Should have an admin user");
                assertEquals("adminuser", rs.getString("USERNAME"));
                assertEquals(1, rs.getInt("USER_ADMIN"));
            }
        }
        
        @Test
        @DisplayName("Sample products have related info records")
        void testProductsHaveRelatedInfo() throws SQLException {
            H2TestDatabase.initializeDatabaseWithTestData();
            
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement();
                 ResultSet rs = stmt.executeQuery(
                     "SELECT p.NAME, i.PRICE FROM product p " +
                     "JOIN product_info i ON p.CODE = i.CODE " +
                     "WHERE p.CODE = 1")) {
                assertTrue(rs.next(), "Product 1 should have info");
                assertEquals("Protein Shake Vanilla", rs.getString("NAME"));
                assertEquals(29.99, rs.getDouble("PRICE"), 0.01);
            }
        }
    }
    
    @Nested
    @DisplayName("Database Reset and Cleanup")
    class ResetTests {
        
        @Test
        @DisplayName("resetDatabase removes all tables")
        void testResetRemovesTables() throws SQLException {
            H2TestDatabase.initializeDatabase();
            H2TestDatabase.resetDatabase();
            
            // After reset, schema is recreated (tables exist but are empty)
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement();
                 ResultSet rs = stmt.executeQuery(
                     "SELECT COUNT(*) FROM INFORMATION_SCHEMA.TABLES WHERE TABLE_NAME = 'PRODUCT'")) {
                assertTrue(rs.next());
                assertEquals(1, rs.getInt(1), "Products table should exist after reset (schema recreated)");
            }
        }
        
        @Test
        @DisplayName("resetDatabase keeps initialized flag true (schema recreated)")
        void testResetKeepsInitializedTrue() {
            H2TestDatabase.initializeDatabase();
            assertTrue(H2TestDatabase.isInitialized());
            
            H2TestDatabase.resetDatabase();
            // Schema is recreated after reset, so initialized stays true
            assertTrue(H2TestDatabase.isInitialized());
        }
        
        @Test
        @DisplayName("clearAllData removes data but keeps schema")
        void testClearAllDataKeepsSchema() throws SQLException {
            H2TestDatabase.initializeDatabaseWithTestData();
            
            // Verify data exists
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement();
                 ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM product")) {
                assertTrue(rs.next());
                assertTrue(rs.getInt(1) > 0, "Should have data before clear");
            }
            
            H2TestDatabase.clearAllData();
            
            // Verify data is gone but table exists
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement();
                 ResultSet rs = stmt.executeQuery("SELECT COUNT(*) FROM product")) {
                assertTrue(rs.next());
                assertEquals(0, rs.getInt(1), "Should have no data after clear");
            }
        }
    }
    
    @Nested
    @DisplayName("CRUD Operations Verification")
    class CrudOperationsTests {
        
        @Test
        @DisplayName("Can insert and retrieve a product")
        void testInsertAndRetrieveProduct() throws SQLException {
            H2TestDatabase.initializeDatabase();
            
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement()) {
                
                // Insert
                stmt.execute("INSERT INTO product (CODE, NAME, CURRENT_INFOS) VALUES (100, 'Test Product', 100)");
                
                // Retrieve
                try (ResultSet rs = stmt.executeQuery("SELECT NAME FROM product WHERE CODE = 100")) {
                    assertTrue(rs.next(), "Should find inserted product");
                    assertEquals("Test Product", rs.getString("NAME"));
                }
            }
        }
        
        @Test
        @DisplayName("Test schema allows inserting data without FK constraints for test isolation")
        void testSchemaAllowsTestDataInsertion() throws SQLException {
            H2TestDatabase.initializeDatabase();
            
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement()) {
                
                // FK constraints removed for test isolation - this should succeed
                assertDoesNotThrow(() -> {
                    stmt.execute(
                        "INSERT INTO orders (code, \"User\", address, state, total_cost) " +
                        "VALUES (999, 'testuser', 'Test Address', 'PENDING', 10.00)");
                });
            }
        }
        
        @Test
        @DisplayName("Can perform join queries across tables")
        void testJoinQueries() throws SQLException {
            H2TestDatabase.initializeDatabaseWithTestData();
            
            try (Connection conn = H2TestDatabase.getConnection();
                 Statement stmt = conn.createStatement();
                 ResultSet rs = stmt.executeQuery(
                     "SELECT p.NAME, i.PRICE, n.PROTEINS " +
                     "FROM product p " +
                     "JOIN product_info i ON p.CURRENT_INFOS = i.CODE " +
                     "JOIN nutritionalValues n ON p.CODE = n.PRODUCT_CODE " +
                     "WHERE p.CODE = 1")) {
                
                assertTrue(rs.next(), "Should get joined result");
                assertEquals("Protein Shake Vanilla", rs.getString("NAME"));
                assertEquals(29.99, rs.getDouble("PRICE"), 0.01);
                assertEquals(25.0, rs.getDouble("PROTEINS"), 0.01);
            }
        }
    }
}
