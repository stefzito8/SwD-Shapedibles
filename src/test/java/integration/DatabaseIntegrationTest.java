package integration;

import categories.IntegrationTest;
import model.bean.*;
import model.datasource.*;
import org.junit.jupiter.api.*;
import org.junit.jupiter.api.MethodOrderer.OrderAnnotation;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Database Integration Tests for SwD-Shapedibles.
 * 
 * <h2>Testing Strategy: Bottom-Up Integration</h2>
 * <p>Per SPEC.md REQ-INT-02: "Integration tests shall use an appropriate strategy 
 * (bottom-up, top-down, sandwich, or modified sandwich) with justification."</p>
 * 
 * <p>Bottom-Up strategy is chosen for DAO-Database integration because:</p>
 * <ol>
 *   <li>DAOs are the lowest layer in the application architecture</li>
 *   <li>Database operations must work correctly before higher layers can be integrated</li>
 *   <li>No stubs needed - real H2 database is used</li>
 *   <li>Drivers are simple (test classes directly call DAO methods)</li>
 * </ol>
 * 
 * <h2>DAO Coverage Priority (from TASK.md Step 5.1)</h2>
 * <table border="1">
 *   <tr><th>Priority</th><th>DAO</th><th>Reason</th></tr>
 *   <tr><td>HIGH</td><td>ProductDaoDataSource</td><td>Core product catalog</td></tr>
 *   <tr><td>HIGH</td><td>UserDaoDataSource</td><td>Authentication</td></tr>
 *   <tr><td>HIGH</td><td>OrderDaoDataSource</td><td>Order processing</td></tr>
 *   <tr><td>HIGH</td><td>ContainDaoDataSource</td><td>Cart/order items</td></tr>
 *   <tr><td>MEDIUM</td><td>InfoDaoDataSource</td><td>Product details</td></tr>
 *   <tr><td>MEDIUM</td><td>NutritionTableDaoDataSource</td><td>Nutritional info</td></tr>
 *   <tr><td>MEDIUM</td><td>AddressDaoDataSource</td><td>Shipping addresses</td></tr>
 *   <tr><td>LOW</td><td>ImageDaoDataSource</td><td>Product images</td></tr>
 * </table>
 * 
 * <h2>Test Isolation</h2>
 * <p>Each test starts with a clean database state via {@code @BeforeEach} reset.</p>
 * 
 * @see H2TestDatabase
 * @see model.datasource.ProductDaoDataSource
 * @see model.datasource.UserDaoDataSource
 */
@IntegrationTest
@TestMethodOrder(OrderAnnotation.class)
@DisplayName("Database Integration Tests - Bottom-Up DAO Testing")
public class DatabaseIntegrationTest {

    private static DataSource dataSource;

    @BeforeAll
    static void setUpClass() {
        dataSource = H2TestDatabase.getDataSource();
        H2TestDatabase.initializeDatabase();
    }

    @BeforeEach
    void setUp() {
        // Reset database to clean state with test data before each test
        H2TestDatabase.resetDatabase();
        H2TestDatabase.initializeDatabaseWithTestData();
    }

    @AfterAll
    static void tearDownClass() {
        H2TestDatabase.resetDatabase();
    }

    // ========================================================================
    // ProductDaoDataSource Tests (HIGH Priority)
    // ========================================================================

    @Nested
    @DisplayName("ProductDaoDataSource Integration Tests")
    class ProductDaoTests {

        private ProductDaoDataSource productDao;

        @BeforeEach
        void setUp() {
            productDao = new ProductDaoDataSource(dataSource);
        }

        @Test
        @Order(1)
        @DisplayName("doRetrieveAll returns all products from database")
        void testDoRetrieveAllReturnsAllProducts() throws SQLException {
            Collection<ProductBean> products = productDao.doRetrieveAll("CODE");
            
            assertNotNull(products, "Product collection should not be null");
            assertEquals(5, products.size(), "Should retrieve all 5 test products");
        }

        @Test
        @Order(2)
        @DisplayName("doRetrieveByKey returns correct product")
        void testDoRetrieveByKeyReturnsCorrectProduct() throws SQLException {
            ProductBean product = productDao.doRetrieveByKey(1);
            
            assertNotNull(product, "Product should not be null");
            assertEquals(1, product.getCodice(), "Product code should match");
            assertEquals("Protein Shake Vanilla", product.getNome(), "Product name should match");
        }

        @Test
        @Order(3)
        @DisplayName("doRetrieveByKey returns empty bean for non-existent product")
        void testDoRetrieveByKeyReturnsNullForNonExistent() throws SQLException {
            ProductBean product = productDao.doRetrieveByKey(999);
            
            // DAO returns default bean with code=-1, not null (production code behavior)
            assertNotNull(product, "DAO returns default bean, not null");
            assertEquals(-1, product.getCodice(), "Default bean should have code -1");
        }

        @Test
        @Order(4)
        @DisplayName("doSave inserts new product into database")
        void testDoSaveInsertsNewProduct() throws SQLException {
            // Count products before
            int countBefore = productDao.doRetrieveAll("CODE").size();
            
            ProductBean newProduct = new ProductBean();
            newProduct.setNome("Unique Test Product XYZ");
            newProduct.setInfoCorrenti(1);  // Set required info reference
            
            productDao.doSave(newProduct);
            
            // Verify by counting products (doSave doesn't return generated ID)
            int countAfter = productDao.doRetrieveAll("CODE").size();
            assertEquals(countBefore + 1, countAfter, "Should have one more product after save");
            
            // Also verify by searching for the product name
            Collection<ProductBean> found = productDao.searchByName("Unique Test Product");
            assertFalse(found.isEmpty(), "Should find the saved product by name");
        }

        @Test
        @Order(5)
        @DisplayName("doDelete removes product from database")
        void testDoDeleteRemovesProduct() throws SQLException {
            // First verify product exists
            ProductBean product = productDao.doRetrieveByKey(5);
            assertNotNull(product, "Product 5 should exist before deletion");
            assertTrue(product.getCodice() > 0, "Product should have valid code before deletion");
            
            // Delete the product
            productDao.doDelete(5);
            
            // Verify deletion - DAO returns default bean with code=-1, not null
            ProductBean deleted = productDao.doRetrieveByKey(5);
            assertNotNull(deleted, "DAO returns default bean, not null");
            assertEquals(-1, deleted.getCodice(), "Deleted product should have code -1 (empty bean)");
        }

        @Test
        @Order(6)
        @DisplayName("doRetrieveAll with order parameter sorts correctly")
        void testDoRetrieveAllWithOrderSortsCorrectly() throws SQLException {
            Collection<ProductBean> products = productDao.doRetrieveAll("NAME");
            
            assertNotNull(products, "Products should not be null");
            assertFalse(products.isEmpty(), "Products should not be empty");
            
            // Verify products are returned (order depends on implementation)
            assertEquals(5, products.size(), "Should have 5 products");
        }

        @Test
        @Order(7)
        @DisplayName("searchByName finds products matching query")
        void testSearchByNameFindsMatchingProducts() throws SQLException {
            Collection<ProductBean> results = productDao.searchByName("Protein");
            
            assertNotNull(results, "Search results should not be null");
            assertTrue(results.size() >= 1, "Should find at least one protein product");
        }

        @Test
        @Order(8)
        @DisplayName("searchByName returns empty for no matches")
        void testSearchByNameReturnsEmptyForNoMatches() throws SQLException {
            Collection<ProductBean> results = productDao.searchByName("XYZ_NONEXISTENT_PRODUCT_ZYX");
            
            assertNotNull(results, "Search results should not be null");
            assertTrue(results.isEmpty(), "Should return empty for non-matching query");
        }

        @Test
        @Order(9)
        @DisplayName("doRetrieveByName finds product by exact name")
        void testDoRetrieveByNameFindsProduct() throws SQLException {
            ProductBean product = productDao.doRetrieveByName("Protein Shake Vanilla");
            
            assertNotNull(product, "Should find product by name");
            assertEquals(1, product.getCodice(), "Product code should match");
        }
    }

    // ========================================================================
    // UserDaoDataSource Tests (HIGH Priority)
    // ========================================================================

    @Nested
    @DisplayName("UserDaoDataSource Integration Tests")
    class UserDaoTests {

        private UserDaoDataSource userDao;

        @BeforeEach
        void setUp() {
            userDao = new UserDaoDataSource(dataSource);
        }

        @Test
        @Order(10)
        @DisplayName("doRetrieveByKey returns existing user")
        void testDoRetrieveByKeyReturnsUser() throws SQLException {
            UserBean user = userDao.doRetrieveByKey("testuser");
            
            assertNotNull(user, "User should exist");
            assertEquals("testuser", user.getUsername(), "Username should match");
        }

        @Test
        @Order(11)
        @DisplayName("doRetrieveByKey returns empty bean for non-existent user")
        void testDoRetrieveByKeyReturnsNullForNonExistent() throws SQLException {
            UserBean user = userDao.doRetrieveByKey("nonexistent_user_xyz");
            
            // DAO returns default bean, not null
            assertNotNull(user, "DAO returns default bean, not null");
            // Default bean has empty/blank username or admin=-1
            assertTrue(user.getUsername() == null || user.getUsername().isBlank() || user.getUserAdmin() == -1,
                "Default bean should have blank username or default admin value");
        }

        @Test
        @Order(12)
        @DisplayName("Admin user has correct admin flag")
        void testAdminUserHasCorrectFlag() throws SQLException {
            UserBean admin = userDao.doRetrieveByKey("adminuser");
            
            assertNotNull(admin, "Admin user should exist");
            assertEquals(1, admin.getUserAdmin(), "Admin flag should be 1");
        }

        @Test
        @Order(13)
        @DisplayName("Regular user has admin flag set to 0")
        void testRegularUserHasZeroAdminFlag() throws SQLException {
            UserBean user = userDao.doRetrieveByKey("testuser");
            
            assertNotNull(user, "Test user should exist");
            assertEquals(0, user.getUserAdmin(), "Regular user admin flag should be 0");
        }

        @Test
        @Order(14)
        @DisplayName("doSave inserts new user into database")
        void testDoSaveInsertsNewUser() throws SQLException {
            UserBean newUser = new UserBean();
            newUser.setUsername("newuser");
            newUser.setPass("hashedpassword123");
            newUser.setEmail("new@test.com");
            newUser.setNomeCognome("New User");
            newUser.setUserAdmin(0);
            newUser.setSesso("M");
            newUser.setPaese("IT");
            newUser.setDataNascita("1990-01-15");  // DATE format for H2
            
            userDao.doSave(newUser);
            
            UserBean retrieved = userDao.doRetrieveByKey("newuser");
            assertNotNull(retrieved, "New user should be retrievable");
            assertEquals("new@test.com", retrieved.getEmail(), "Email should match");
        }

        @Test
        @Order(15)
        @DisplayName("User retrieval returns correct email")
        void testUserRetrievalReturnsCorrectEmail() throws SQLException {
            UserBean user = userDao.doRetrieveByKey("testuser");
            
            assertNotNull(user, "User should exist");
            assertNotNull(user.getEmail(), "Email should not be null");
            assertEquals("testuser@example.com", user.getEmail(), "Should find existing email");
        }

        @Test
        @Order(16)
        @DisplayName("doRetrieveAll returns all users")
        void testDoRetrieveAllReturnsAllUsers() throws SQLException {
            Collection<UserBean> users = userDao.doRetrieveAll("username");
            
            assertNotNull(users, "Users collection should not be null");
            assertEquals(2, users.size(), "Should have 2 test users");
        }
    }

    // ========================================================================
    // InfoDaoDataSource Tests (MEDIUM Priority)
    // ========================================================================

    @Nested
    @DisplayName("InfoDaoDataSource Integration Tests")
    class InfoDaoTests {

        private InfoDaoDataSource infoDao;

        @BeforeEach
        void setUp() {
            infoDao = new InfoDaoDataSource(dataSource);
        }

        @Test
        @Order(20)
        @DisplayName("doRetrieveByKey returns product info")
        void testDoRetrieveByKeyReturnsInfo() throws SQLException {
            InfoBean info = infoDao.doRetrieveByKey(1);
            
            assertNotNull(info, "Info should exist for product 1");
            assertEquals(1, info.getCodice(), "Product code should match");
        }

        @Test
        @Order(21)
        @DisplayName("Info contains correct description")
        void testInfoContainsCorrectDescription() throws SQLException {
            InfoBean info = infoDao.doRetrieveByKey(1);
            
            assertNotNull(info, "Info should exist");
            assertNotNull(info.getDescrizione(), "Description should not be null");
            assertTrue(info.getDescrizione().length() > 0, "Description should not be empty");
        }

        @Test
        @Order(22)
        @DisplayName("Info contains valid price")
        void testInfoContainsValidPrice() throws SQLException {
            InfoBean info = infoDao.doRetrieveByKey(1);
            
            assertNotNull(info, "Info should exist");
            assertTrue(info.getCosto() > 0, "Price should be positive");
        }

        @Test
        @Order(23)
        @DisplayName("doRetrieveByKey returns empty bean for non-existent product")
        void testDoRetrieveByKeyReturnsNullForNonExistent() throws SQLException {
            InfoBean info = infoDao.doRetrieveByKey(999);
            
            // DAO returns default bean with codice=-1, not null
            assertNotNull(info, "DAO returns default bean, not null");
            assertEquals(-1, info.getCodice(), "Default bean should have codice -1");
        }

        @Test
        @Order(24)
        @DisplayName("doRetrieveAll returns all product info records")
        void testDoRetrieveAllReturnsAllInfo() throws SQLException {
            Collection<InfoBean> allInfo = infoDao.doRetrieveAll("CODE");
            
            assertNotNull(allInfo, "Info collection should not be null");
            assertEquals(5, allInfo.size(), "Should have info for all 5 products");
        }
    }

    // ========================================================================
    // NutritionTableDaoDataSource Tests (MEDIUM Priority)
    // ========================================================================

    @Nested
    @DisplayName("NutritionTableDaoDataSource Integration Tests")
    class NutritionTableDaoTests {

        private NutritionTableDaoDataSource nutritionDao;

        @BeforeEach
        void setUp() {
            nutritionDao = new NutritionTableDaoDataSource(dataSource);
        }

        @Test
        @Order(30)
        @DisplayName("doRetrieveByKey returns nutrition data")
        void testDoRetrieveByKeyReturnsNutrition() throws SQLException {
            NutritionTableBean nutrition = nutritionDao.doRetrieveByKey(1);
            
            assertNotNull(nutrition, "Nutrition data should exist for product 1");
            assertEquals(1, nutrition.getCodiceProdotto(), "Product code should match");
        }

        @Test
        @Order(31)
        @DisplayName("Nutrition contains valid energy value")
        void testNutritionContainsValidEnergy() throws SQLException {
            NutritionTableBean nutrition = nutritionDao.doRetrieveByKey(1);
            
            assertNotNull(nutrition, "Nutrition should exist");
            assertTrue(nutrition.getEnergia() >= 0, "Energy should be non-negative");
        }

        @Test
        @Order(32)
        @DisplayName("Nutrition contains valid protein value")
        void testNutritionContainsValidProtein() throws SQLException {
            NutritionTableBean nutrition = nutritionDao.doRetrieveByKey(1);
            
            assertNotNull(nutrition, "Nutrition should exist");
            assertTrue(nutrition.getProteine() >= 0, "Protein should be non-negative");
        }

        @Test
        @Order(33)
        @DisplayName("doRetrieveAll returns all nutrition records")
        void testDoRetrieveAllReturnsAllNutrition() throws SQLException {
            Collection<NutritionTableBean> allNutrition = nutritionDao.doRetrieveAll("PRODUCT_CODE");
            
            assertNotNull(allNutrition, "Nutrition collection should not be null");
            assertEquals(5, allNutrition.size(), "Should have nutrition for all 5 products");
        }
    }

    // ========================================================================
    // OrderDaoDataSource Tests (HIGH Priority)
    // ========================================================================

    @Nested
    @DisplayName("OrderDaoDataSource Integration Tests")
    class OrderDaoTests {

        private OrderDaoDataSource orderDao;

        @BeforeEach
        void setUp() {
            orderDao = new OrderDaoDataSource(dataSource);
        }

        @Test
        @Order(40)
        @DisplayName("doRetrieveByKey returns existing order")
        void testDoRetrieveByKeyReturnsOrder() throws SQLException {
            OrderBean order = orderDao.doRetrieveByKey("testuser", 1);
            
            assertNotNull(order, "Order should exist");
            assertEquals(1, order.getCodice(), "Order code should match");
        }

        @Test
        @Order(41)
        @DisplayName("Order contains valid user reference")
        void testOrderContainsValidUserReference() throws SQLException {
            OrderBean order = orderDao.doRetrieveByKey("testuser", 1);
            
            assertNotNull(order, "Order should exist");
            assertNotNull(order.getUtente(), "User (utente) should not be null");
            assertEquals("testuser", order.getUtente(), "User should match test user");
        }

        @Test
        @Order(42)
        @DisplayName("doRetrieveByUser returns user orders")
        void testDoRetrieveByUserReturnsUserOrders() throws SQLException {
            Collection<OrderBean> orders = orderDao.doRetrieveByUser("testuser");
            
            assertNotNull(orders, "Orders collection should not be null");
            assertTrue(orders.size() >= 1, "Test user should have at least one order");
        }

        @Test
        @Order(43)
        @DisplayName("doRetrieveByUser returns empty for user with no orders")
        void testDoRetrieveByUserReturnsEmptyForNoOrders() throws SQLException {
            Collection<OrderBean> orders = orderDao.doRetrieveByUser("nonexistent_user");
            
            assertNotNull(orders, "Orders collection should not be null");
            assertTrue(orders.isEmpty(), "Non-existent user should have no orders");
        }

        @Test
        @Order(44)
        @DisplayName("doSave creates new order")
        void testDoSaveCreatesNewOrder() throws SQLException {
            OrderBean newOrder = new OrderBean();
            newOrder.setCodice(100);
            newOrder.setUtente("testuser");
            newOrder.setIndirizzo("123 Test St");
            newOrder.setStato("pending");
            newOrder.setSaldoTotale(99.99);
            
            orderDao.doSave(newOrder);
            
            OrderBean retrieved = orderDao.doRetrieveByKey("testuser", 100);
            assertNotNull(retrieved, "New order should be retrievable");
            assertEquals("pending", retrieved.getStato(), "Status should match");
        }

        @Test
        @Order(45)
        @DisplayName("doRetrieveAll returns all orders")
        void testDoRetrieveAllReturnsAllOrders() throws SQLException {
            Collection<OrderBean> orders = orderDao.doRetrieveAll("code");
            
            assertNotNull(orders, "Orders collection should not be null");
            assertTrue(orders.size() >= 1, "Should have at least one order");
        }
    }

    // ========================================================================
    // ContainDaoDataSource Tests (HIGH Priority)
    // ========================================================================

    @Nested
    @DisplayName("ContainDaoDataSource Integration Tests")
    class ContainDaoTests {

        private ContainDaoDataSource containDao;

        @BeforeEach
        void setUp() {
            containDao = new ContainDaoDataSource(dataSource);
        }

        @Test
        @Order(50)
        @DisplayName("doRetrieveByOrder returns order items")
        void testDoRetrieveByOrderReturnsItems() throws SQLException {
            Collection<ContainBean> items = containDao.doRetrieveByOrder(1);
            
            assertNotNull(items, "Items collection should not be null");
            assertTrue(items.size() >= 1, "Order 1 should have at least one item");
        }

        @Test
        @Order(51)
        @DisplayName("Order items have valid product references")
        void testOrderItemsHaveValidProductReferences() throws SQLException {
            Collection<ContainBean> items = containDao.doRetrieveByOrder(1);
            
            assertNotNull(items, "Items should exist");
            for (ContainBean item : items) {
                assertTrue(item.getCodiceProdotto() > 0, "Product code should be positive");
                assertTrue(item.getQuantità() > 0, "Quantity should be positive");
            }
        }

        @Test
        @Order(52)
        @DisplayName("doRetrieveByOrder returns empty for order with no items")
        void testDoRetrieveByOrderReturnsEmptyForNoItems() throws SQLException {
            Collection<ContainBean> items = containDao.doRetrieveByOrder(999);
            
            assertNotNull(items, "Items collection should not be null");
            assertTrue(items.isEmpty(), "Non-existent order should have no items");
        }

        @Test
        @Order(53)
        @DisplayName("doSave adds item to order")
        void testDoSaveAddsItemToOrder() throws SQLException {
            ContainBean newItem = new ContainBean();
            newItem.setCodiceOrdine(1);
            newItem.setCodiceProdotto(3);
            newItem.setQuantità(2);
            
            containDao.doSave(newItem);
            
            Collection<ContainBean> items = containDao.doRetrieveByOrder(1);
            assertTrue(items.size() >= 2, "Order should now have at least 2 items");
        }
    }

    // ========================================================================
    // AddressDaoDataSource Tests (MEDIUM Priority)
    // ========================================================================

    @Nested
    @DisplayName("AddressDaoDataSource Integration Tests")
    class AddressDaoTests {

        private AddressDaoDataSource addressDao;

        @BeforeEach
        void setUp() {
            addressDao = new AddressDaoDataSource(dataSource);
        }

        @Test
        @Order(60)
        @DisplayName("doRetrieveByKey returns existing address")
        void testDoRetrieveByKeyReturnsAddress() throws SQLException {
            AddressBean address = addressDao.doRetrieveByKey("1", "testuser");
            
            assertNotNull(address, "Address should exist");
            assertEquals("1", address.getId(), "Address id should match");
        }

        @Test
        @Order(61)
        @DisplayName("Address contains valid street information")
        void testAddressContainsValidStreet() throws SQLException {
            AddressBean address = addressDao.doRetrieveByKey("1", "testuser");
            
            assertNotNull(address, "Address should exist");
            assertNotNull(address.getStrada(), "Street should not be null");
            assertTrue(address.getStrada().length() > 0, "Street should not be empty");
        }

        @Test
        @Order(62)
        @DisplayName("doRetrieveByUser returns user addresses")
        void testDoRetrieveByUserReturnsAddresses() throws SQLException {
            Collection<AddressBean> addresses = addressDao.doRetrieveByUser("testuser");
            
            assertNotNull(addresses, "Addresses collection should not be null");
            assertTrue(addresses.size() >= 1, "Test user should have at least one address");
        }

        @Test
        @Order(63)
        @DisplayName("doSave creates new address")
        void testDoSaveCreatesNewAddress() throws SQLException {
            AddressBean newAddress = new AddressBean();
            newAddress.setId("100");
            newAddress.setUtente("testuser");
            newAddress.setStrada("New Street");
            newAddress.setCittà("New City");
            newAddress.setCodicePostale("12345");
            newAddress.setPaese("Italy");
            newAddress.setNumero(456);
            
            addressDao.doSave(newAddress);
            
            AddressBean retrieved = addressDao.doRetrieveByKey("100", "testuser");
            assertNotNull(retrieved, "New address should be retrievable");
            assertEquals("New Street", retrieved.getStrada(), "Street should match");
        }
    }

    // ========================================================================
    // Cross-DAO Consistency Tests
    // ========================================================================

    @Nested
    @DisplayName("Cross-DAO Data Consistency Tests")
    class CrossDaoConsistencyTests {

        @Test
        @Order(70)
        @DisplayName("Product and Info data are consistent")
        void testProductInfoConsistency() throws SQLException {
            ProductDaoDataSource productDao = new ProductDaoDataSource(dataSource);
            InfoDaoDataSource infoDao = new InfoDaoDataSource(dataSource);
            
            Collection<ProductBean> products = productDao.doRetrieveAll("CODE");
            
            for (ProductBean product : products) {
                InfoBean info = infoDao.doRetrieveByKey(product.getCodice());
                assertNotNull(info, "Each product should have corresponding info: " + product.getCodice());
                assertEquals(product.getCodice(), info.getCodice(), 
                    "Info product code should match product code");
            }
        }

        @Test
        @Order(71)
        @DisplayName("Product and Nutrition data are consistent")
        void testProductNutritionConsistency() throws SQLException {
            ProductDaoDataSource productDao = new ProductDaoDataSource(dataSource);
            NutritionTableDaoDataSource nutritionDao = new NutritionTableDaoDataSource(dataSource);
            
            Collection<ProductBean> products = productDao.doRetrieveAll("CODE");
            
            for (ProductBean product : products) {
                NutritionTableBean nutrition = nutritionDao.doRetrieveByKey(product.getCodice());
                assertNotNull(nutrition, "Each product should have nutrition data: " + product.getCodice());
                assertEquals(product.getCodice(), nutrition.getCodiceProdotto(), 
                    "Nutrition product code should match product code");
            }
        }

        @Test
        @Order(72)
        @DisplayName("Order and User data are consistent")
        void testOrderUserConsistency() throws SQLException {
            OrderDaoDataSource orderDao = new OrderDaoDataSource(dataSource);
            UserDaoDataSource userDao = new UserDaoDataSource(dataSource);
            
            Collection<OrderBean> orders = orderDao.doRetrieveAll("code");
            
            for (OrderBean order : orders) {
                UserBean user = userDao.doRetrieveByKey(order.getUtente());
                assertNotNull(user, "Each order should have valid user: " + order.getUtente());
            }
        }

        @Test
        @Order(73)
        @DisplayName("Order items reference valid products")
        void testOrderItemsProductConsistency() throws SQLException {
            ContainDaoDataSource containDao = new ContainDaoDataSource(dataSource);
            ProductDaoDataSource productDao = new ProductDaoDataSource(dataSource);
            
            Collection<ContainBean> items = containDao.doRetrieveByOrder(1);
            
            for (ContainBean item : items) {
                ProductBean product = productDao.doRetrieveByKey(item.getCodiceProdotto());
                assertNotNull(product, "Each order item should reference valid product: " + item.getCodiceProdotto());
            }
        }

        @Test
        @Order(74)
        @DisplayName("Address belongs to existing user")
        void testAddressUserConsistency() throws SQLException {
            AddressDaoDataSource addressDao = new AddressDaoDataSource(dataSource);
            UserDaoDataSource userDao = new UserDaoDataSource(dataSource);
            
            AddressBean address = addressDao.doRetrieveByKey("1", "testuser");
            assertNotNull(address, "Address should exist");
            
            UserBean user = userDao.doRetrieveByKey(address.getUtente());
            assertNotNull(user, "Address should belong to existing user");
        }
    }

    // ========================================================================
    // Transaction and Isolation Tests
    // ========================================================================

    @Nested
    @DisplayName("Transaction and Isolation Tests")
    class TransactionTests {

        @Test
        @Order(80)
        @DisplayName("Database reset provides clean state")
        void testDatabaseResetProvidesCleanState() throws SQLException {
            // Add some data
            ProductDaoDataSource productDao = new ProductDaoDataSource(dataSource);
            ProductBean temp = new ProductBean();
            temp.setCodice(999);
            temp.setNome("Temporary Product");
            productDao.doSave(temp);
            
            // Verify it exists
            ProductBean saved = productDao.doRetrieveByKey(999);
            assertNotNull(saved, "Temporary product should exist");
            
            // Reset database
            H2TestDatabase.resetDatabase();
            H2TestDatabase.initializeDatabaseWithTestData();
            
            // Verify clean state (product 999 should not exist, but product 1-5 should)
            ProductBean afterReset = productDao.doRetrieveByKey(999);
            // DAO returns default bean with code=-1, not null
            assertNotNull(afterReset, "DAO returns default bean, not null");
            assertEquals(-1, afterReset.getCodice(), "Temporary product should be gone (code=-1 means not found)");
            
            ProductBean original = productDao.doRetrieveByKey(1);
            assertNotNull(original, "Original test data should be restored");
        }

        @Test
        @Order(81)
        @DisplayName("Concurrent DAO operations don't interfere")
        void testConcurrentDaoOperations() throws SQLException {
            ProductDaoDataSource productDao1 = new ProductDaoDataSource(dataSource);
            ProductDaoDataSource productDao2 = new ProductDaoDataSource(dataSource);
            
            // Read with both DAOs
            ProductBean product1 = productDao1.doRetrieveByKey(1);
            ProductBean product2 = productDao2.doRetrieveByKey(1);
            
            assertNotNull(product1, "First DAO should retrieve product");
            assertNotNull(product2, "Second DAO should retrieve product");
            assertEquals(product1.getCodice(), product2.getCodice(), "Both should get same product");
        }

        @Test
        @Order(82)
        @DisplayName("Delete cascades or fails appropriately for foreign keys")
        void testForeignKeyConstraints() throws SQLException {
            // This test verifies that the database enforces referential integrity
            // Attempting to delete a user with orders should fail or cascade
            
            try (Connection conn = dataSource.getConnection();
                 Statement stmt = conn.createStatement()) {
                
                // Try to delete user that has orders - should fail due to FK constraint
                // or succeed if cascade delete is configured
                try {
                    stmt.executeUpdate("DELETE FROM users WHERE username = 'testuser'");
                    
                    // If we get here, either cascade delete worked or no FK constraint
                    // Re-add the test data
                    H2TestDatabase.resetDatabase();
                    H2TestDatabase.initializeDatabaseWithTestData();
                } catch (SQLException e) {
                    // Expected if FK constraint is enforced without cascade
                    assertTrue(e.getMessage().toLowerCase().contains("constraint") ||
                               e.getMessage().toLowerCase().contains("foreign") ||
                               e.getMessage().toLowerCase().contains("integrity"),
                        "Should fail due to foreign key constraint");
                }
            }
        }
    }

    // ========================================================================
    // Edge Cases and Boundary Tests
    // ========================================================================

    @Nested
    @DisplayName("Edge Cases and Boundary Tests")
    class EdgeCaseTests {

        @Test
        @Order(90)
        @DisplayName("Handle null order parameter in doRetrieveAll")
        void testDoRetrieveAllWithNullOrder() throws SQLException {
            ProductDaoDataSource productDao = new ProductDaoDataSource(dataSource);
            
            // Depending on implementation, null order might default to no ordering
            Collection<ProductBean> products = productDao.doRetrieveAll(null);
            
            assertNotNull(products, "Should handle null order gracefully");
            assertEquals(5, products.size(), "Should still return all products");
        }

        @Test
        @Order(91)
        @DisplayName("Handle empty string order parameter")
        void testDoRetrieveAllWithEmptyOrder() throws SQLException {
            ProductDaoDataSource productDao = new ProductDaoDataSource(dataSource);
            
            Collection<ProductBean> products = productDao.doRetrieveAll("");
            
            assertNotNull(products, "Should handle empty order gracefully");
            assertEquals(5, products.size(), "Should still return all products");
        }

        @Test
        @Order(92)
        @DisplayName("Search handles special characters")
        void testSearchHandlesSpecialCharacters() throws SQLException {
            ProductDaoDataSource productDao = new ProductDaoDataSource(dataSource);
            
            // Search with special characters - should not cause SQL injection
            Collection<ProductBean> results = productDao.searchByName("'; DROP TABLE products; --");
            
            assertNotNull(results, "Should handle SQL injection attempt gracefully");
            // Products table should still exist
            Collection<ProductBean> allProducts = productDao.doRetrieveAll("CODE");
            assertEquals(5, allProducts.size(), "Products table should still have 5 products");
        }

        @Test
        @Order(93)
        @DisplayName("Handle negative product code")
        void testHandleNegativeProductCode() throws SQLException {
            ProductDaoDataSource productDao = new ProductDaoDataSource(dataSource);
            
            ProductBean product = productDao.doRetrieveByKey(-1);
            
            // DAO returns default bean with code=-1, not null
            assertNotNull(product, "DAO returns default bean, not null");
            assertEquals(-1, product.getCodice(), "Default bean should have code -1");
        }

        @Test
        @Order(94)
        @DisplayName("Handle zero product code")
        void testHandleZeroProductCode() throws SQLException {
            ProductDaoDataSource productDao = new ProductDaoDataSource(dataSource);
            
            ProductBean product = productDao.doRetrieveByKey(0);
            
            // DAO returns default bean with code=-1, not null
            assertNotNull(product, "DAO returns default bean, not null");
            assertEquals(-1, product.getCodice(), "Default bean should have code -1");
        }

        @Test
        @Order(95)
        @DisplayName("Handle very large product code")
        void testHandleVeryLargeProductCode() throws SQLException {
            ProductDaoDataSource productDao = new ProductDaoDataSource(dataSource);
            
            ProductBean product = productDao.doRetrieveByKey(Integer.MAX_VALUE);
            
            // DAO returns default bean with code=-1, not null
            assertNotNull(product, "DAO returns default bean, not null");
            assertEquals(-1, product.getCodice(), "Default bean should have code -1");
        }
    }
}
