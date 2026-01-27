package benchmark;

import model.Cart;
import model.bean.ProductBean;
import model.bean.UserBean;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.TimeUnit;

/**
 * JMH Microbenchmarks for Controller layer operations.
 * 
 * <p>Controllers are performance-critical because:</p>
 * <ul>
 *   <li>Every HTTP request passes through a controller</li>
 *   <li>Request parameter parsing and validation</li>
 *   <li>Session attribute management (read/write)</li>
 *   <li>Action routing logic (switch/if-else chains)</li>
 *   <li>Response preparation (forward vs redirect)</li>
 *   <li>JSON serialization for AJAX responses</li>
 * </ul>
 * 
 * <p>Based on the project's controller classes:</p>
 * <ul>
 *   <li>Cart.java - add/delete/update actions</li>
 *   <li>Checkout.java - order processing</li>
 *   <li>Search.java - query processing</li>
 *   <li>Login.java - authentication flow</li>
 *   <li>Register.java - validation chains</li>
 * </ul>
 */
@BenchmarkMode({Mode.AverageTime, Mode.Throughput})
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Thread)
@Warmup(iterations = 3, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 2, jvmArgs = {"-Xms128M", "-Xmx128M"})
public class ControllerBenchmark {

    // Simulated request parameters
    private Map<String, String> requestParams;
    
    // Simulated session attributes
    private Map<String, Object> sessionAttributes;
    
    // Pre-created objects for benchmarks
    private UserBean regularUser;
    private UserBean adminUser;
    private Cart cart;
    private ProductBean testProduct;

    @Setup(Level.Trial)
    public void setUp() {
        // Initialize request parameters (typical Cart request)
        requestParams = new HashMap<>();
        requestParams.put("productId", "123");
        requestParams.put("quantity", "2");
        requestParams.put("action", "addC");
        requestParams.put("username", "testuser");
        requestParams.put("email", "test@example.com");
        requestParams.put("password", "securePassword123");
        requestParams.put("searchQuery", "protein powder");
        
        // Initialize users
        regularUser = new UserBean();
        regularUser.setUsername("testuser");
        regularUser.setEmail("test@example.com");
        regularUser.setUserAdmin(0);
        
        adminUser = new UserBean();
        adminUser.setUsername("admin");
        adminUser.setEmail("admin@example.com");
        adminUser.setUserAdmin(1);
        
        // Initialize cart with products
        cart = new Cart();
        testProduct = new ProductBean();
        testProduct.setCodice(123);
        testProduct.setNome("Test Product");
        testProduct.setInfoCorrenti(1);
        cart.addProduct(testProduct);
        
        // Initialize session attributes
        sessionAttributes = new HashMap<>();
        sessionAttributes.put("LoggedUser", regularUser);
        sessionAttributes.put("cart", cart);
        sessionAttributes.put("Products", null);
    }

    // ==================== PARAMETER EXTRACTION ====================

    /**
     * Benchmark: Extract and parse integer parameter.
     * Common pattern in CartServlet, ProductDetailsServlet.
     */
    @Benchmark
    public void parameterExtractionInteger(Blackhole bh) {
        String productIdStr = requestParams.get("productId");
        int productId = Integer.parseInt(productIdStr);
        bh.consume(productId);
    }

    /**
     * Benchmark: Extract and parse multiple parameters.
     * Cart operations require productId and sometimes quantity.
     */
    @Benchmark
    public void parameterExtractionMultiple(Blackhole bh) {
        String productIdStr = requestParams.get("productId");
        String quantityStr = requestParams.get("quantity");
        String action = requestParams.get("action");
        
        int productId = Integer.parseInt(productIdStr);
        int quantity = Integer.parseInt(quantityStr);
        
        bh.consume(productId);
        bh.consume(quantity);
        bh.consume(action);
    }

    /**
     * Benchmark: Null-safe parameter extraction.
     * Defensive pattern used throughout controllers.
     */
    @Benchmark
    public void parameterExtractionNullSafe(Blackhole bh) {
        String param = requestParams.get("nonexistent");
        String value = (param != null) ? param : "";
        boolean isEmpty = value.isEmpty();
        bh.consume(isEmpty);
    }

    // ==================== SESSION MANAGEMENT ====================

    /**
     * Benchmark: Session attribute retrieval (single).
     * Most common operation - getting logged user.
     */
    @Benchmark
    public void sessionGetSingleAttribute(Blackhole bh) {
        Object user = sessionAttributes.get("LoggedUser");
        bh.consume(user);
    }

    /**
     * Benchmark: Session attribute retrieval (multiple).
     * Controllers often check user AND cart.
     */
    @Benchmark
    public void sessionGetMultipleAttributes(Blackhole bh) {
        Object user = sessionAttributes.get("LoggedUser");
        Object cart = sessionAttributes.get("cart");
        Object products = sessionAttributes.get("Products");
        bh.consume(user);
        bh.consume(cart);
        bh.consume(products);
    }

    /**
     * Benchmark: Session attribute write.
     * Setting cart after modification.
     */
    @Benchmark
    public void sessionSetAttribute(Blackhole bh) {
        sessionAttributes.put("cart", cart);
        bh.consume(sessionAttributes);
    }

    /**
     * Benchmark: Cart initialization check pattern.
     * Standard pattern: get cart, create if null.
     */
    @Benchmark
    public void sessionCartInitialization(Blackhole bh) {
        Cart sessionCart = (Cart) sessionAttributes.get("cart");
        if (sessionCart == null) {
            sessionCart = new Cart();
            sessionAttributes.put("cart", sessionCart);
        }
        bh.consume(sessionCart);
    }

    // ==================== ACTION ROUTING ====================

    /**
     * Benchmark: Action routing via equalsIgnoreCase.
     * Pattern used in Cart.java servlet.
     */
    @Benchmark
    public void actionRoutingEqualsIgnoreCase(Blackhole bh) {
        String action = requestParams.get("action");
        String result;
        
        if (action.equalsIgnoreCase("addC")) {
            result = "add";
        } else if (action.equalsIgnoreCase("deleteC")) {
            result = "delete";
        } else if (action.equalsIgnoreCase("updateC")) {
            result = "update";
        } else if (action.equalsIgnoreCase("clearC")) {
            result = "clear";
        } else {
            result = "unknown";
        }
        
        bh.consume(result);
    }

    /**
     * Benchmark: Action routing via switch statement.
     * More performant alternative pattern.
     */
    @Benchmark
    public void actionRoutingSwitch(Blackhole bh) {
        String action = requestParams.get("action").toLowerCase();
        String result;
        
        switch (action) {
            case "addc":
                result = "add";
                break;
            case "deletec":
                result = "delete";
                break;
            case "updatec":
                result = "update";
                break;
            case "clearc":
                result = "clear";
                break;
            default:
                result = "unknown";
        }
        
        bh.consume(result);
    }

    /**
     * Benchmark: Null action check before routing.
     * Defensive pattern to prevent NPE.
     */
    @Benchmark
    public void actionRoutingWithNullCheck(Blackhole bh) {
        String action = requestParams.get("action");
        boolean shouldProcess = false;
        
        if (action != null) {
            if (action.equalsIgnoreCase("addC")) {
                shouldProcess = true;
            } else if (action.equalsIgnoreCase("deleteC")) {
                shouldProcess = true;
            }
        }
        
        bh.consume(shouldProcess);
    }

    // ==================== AJAX DETECTION ====================

    /**
     * Benchmark: AJAX request detection.
     * Used in Cart, Search, Login servlets.
     */
    @Benchmark
    public void ajaxDetection(Blackhole bh) {
        String xRequestedWith = "XMLHttpRequest";
        boolean isAjax = "XMLHttpRequest".equals(xRequestedWith);
        bh.consume(isAjax);
    }

    /**
     * Benchmark: AJAX detection with null safety.
     * Header may be null for non-AJAX requests.
     */
    @Benchmark
    public void ajaxDetectionNullSafe(Blackhole bh) {
        String xRequestedWith = null; // Simulates non-AJAX request
        boolean isAjax = "XMLHttpRequest".equals(xRequestedWith);
        bh.consume(isAjax);
    }

    // ==================== INPUT VALIDATION ====================

    /**
     * Benchmark: Username validation.
     * RegisterServlet validation pattern.
     */
    @Benchmark
    public void validationUsername(Blackhole bh) {
        String username = requestParams.get("username");
        boolean valid = username != null 
            && !username.trim().isEmpty()
            && username.length() >= 3
            && username.length() <= 50;
        bh.consume(valid);
    }

    /**
     * Benchmark: Email validation (basic).
     * Simple contains check used in the project.
     */
    @Benchmark
    public void validationEmailBasic(Blackhole bh) {
        String email = requestParams.get("email");
        boolean valid = email != null 
            && email.contains("@")
            && email.contains(".");
        bh.consume(valid);
    }

    /**
     * Benchmark: Password validation.
     * Length and complexity check.
     */
    @Benchmark
    public void validationPassword(Blackhole bh) {
        String password = requestParams.get("password");
        boolean valid = password != null
            && password.length() >= 8
            && password.length() <= 128;
        bh.consume(valid);
    }

    /**
     * Benchmark: Full registration validation chain.
     * All validations in sequence as in RegisterServlet.
     */
    @Benchmark
    public void validationFullChain(Blackhole bh) {
        String username = requestParams.get("username");
        String email = requestParams.get("email");
        String password = requestParams.get("password");
        
        boolean valid = true;
        
        // Username validation
        valid = valid && username != null && !username.trim().isEmpty();
        valid = valid && username.length() >= 3 && username.length() <= 50;
        
        // Email validation
        valid = valid && email != null && email.contains("@");
        
        // Password validation
        valid = valid && password != null && password.length() >= 8;
        
        bh.consume(valid);
    }

    // ==================== SEARCH PROCESSING ====================

    /**
     * Benchmark: Search query sanitization.
     * Input cleaning before database query.
     */
    @Benchmark
    public void searchQuerySanitization(Blackhole bh) {
        String rawQuery = requestParams.get("searchQuery");
        String sanitized = rawQuery.trim().toLowerCase();
        bh.consume(sanitized);
    }

    /**
     * Benchmark: Search query to SQL LIKE pattern.
     * Wildcard preparation for database search.
     */
    @Benchmark
    public void searchQueryToLikePattern(Blackhole bh) {
        String rawQuery = requestParams.get("searchQuery");
        String sanitized = rawQuery.trim().toLowerCase();
        String likePattern = "%" + sanitized + "%";
        bh.consume(likePattern);
    }

    /**
     * Benchmark: Search query with SQL injection prevention.
     * Escaping single quotes.
     */
    @Benchmark
    public void searchQuerySqlSafe(Blackhole bh) {
        String rawQuery = requestParams.get("searchQuery");
        String sanitized = rawQuery.trim()
            .toLowerCase()
            .replace("'", "''");
        String likePattern = "%" + sanitized + "%";
        bh.consume(likePattern);
    }

    // ==================== REDIRECT PATH BUILDING ====================

    /**
     * Benchmark: Simple redirect path.
     * After cart operation, redirect to cart page.
     */
    @Benchmark
    public void redirectPathSimple(Blackhole bh) {
        String contextPath = "/shapedibles";
        String redirectPath = contextPath + "/Cart";
        bh.consume(redirectPath);
    }

    /**
     * Benchmark: Redirect path with query parameters.
     * Include success/error indicators.
     */
    @Benchmark
    public void redirectPathWithParams(Blackhole bh) {
        String contextPath = "/shapedibles";
        String action = "added";
        String redirectPath = contextPath + "/Cart?action=" + action + "&success=true";
        bh.consume(redirectPath);
    }

    /**
     * Benchmark: Forward path determination.
     * JSP path based on action result.
     */
    @Benchmark
    public void forwardPathDetermination(Blackhole bh) {
        boolean isAjax = false;
        String forwardPath;
        
        if (isAjax) {
            forwardPath = null; // No forward for AJAX
        } else {
            forwardPath = "/WEB-INF/jsp/pages/cart.jsp";
        }
        
        bh.consume(forwardPath);
    }

    // ==================== ADMIN CHECK ====================

    /**
     * Benchmark: Admin role verification.
     * Used in ProductAdmin, ProductEdit, ProductUpload.
     */
    @Benchmark
    public void adminRoleCheck(Blackhole bh) {
        UserBean user = (UserBean) sessionAttributes.get("LoggedUser");
        boolean isAdmin = user != null && user.getUserAdmin() == 1;
        bh.consume(isAdmin);
    }

    /**
     * Benchmark: Admin access decision.
     * Full check with redirect determination.
     */
    @Benchmark
    public void adminAccessDecision(Blackhole bh) {
        UserBean user = (UserBean) sessionAttributes.get("LoggedUser");
        String result;
        
        if (user == null) {
            result = "redirect:login";
        } else if (user.getUserAdmin() != 1) {
            result = "redirect:home";
        } else {
            result = "proceed";
        }
        
        bh.consume(result);
    }

    // ==================== JSON RESPONSE BUILDING ====================

    /**
     * Benchmark: Simple JSON response map creation.
     * Used for AJAX responses in Cart servlet.
     */
    @Benchmark
    public void jsonResponseMapCreation(Blackhole bh) {
        Map<String, Object> responseData = new HashMap<>();
        responseData.put("success", true);
        responseData.put("cartSize", cart.getCartSize());
        responseData.put("message", "Product added to cart");
        bh.consume(responseData);
    }

    /**
     * Benchmark: JSON response with error info.
     * Error response structure.
     */
    @Benchmark
    public void jsonResponseError(Blackhole bh) {
        Map<String, Object> responseData = new HashMap<>();
        responseData.put("success", false);
        responseData.put("error", "Product not found");
        responseData.put("errorCode", 404);
        bh.consume(responseData);
    }

    // ==================== COMPLETE FLOW SIMULATIONS ====================

    /**
     * Benchmark: Complete Cart add flow (without DB).
     * Simulates the full controller logic path.
     */
    @Benchmark
    public void completeCartAddFlow(Blackhole bh) {
        // 1. Check AJAX
        boolean isAjax = true;
        
        // 2. Get session cart
        Cart sessionCart = (Cart) sessionAttributes.get("cart");
        if (sessionCart == null) {
            sessionCart = new Cart();
        }
        
        // 3. Parse parameters
        String action = requestParams.get("action");
        int productId = Integer.parseInt(requestParams.get("productId"));
        
        // 4. Route action
        if (action != null && action.equalsIgnoreCase("addC")) {
            // Would call DAO here, but we simulate with existing product
            sessionCart.addProduct(testProduct);
        }
        
        // 5. Update session
        sessionAttributes.put("cart", sessionCart);
        
        // 6. Build response
        Map<String, Object> response = new HashMap<>();
        response.put("cartSize", sessionCart.getCartSize());
        
        bh.consume(response);
    }

    /**
     * Benchmark: Complete Search flow (without DB).
     * Simulates search controller logic.
     */
    @Benchmark
    public void completeSearchFlow(Blackhole bh) {
        // 1. Get search query
        String query = requestParams.get("searchQuery");
        
        // 2. Validate
        boolean valid = query != null && !query.trim().isEmpty();
        
        // 3. Sanitize
        String searchTerm = null;
        if (valid) {
            searchTerm = query.trim().toLowerCase();
            searchTerm = "%" + searchTerm + "%";
        }
        
        // 4. Would execute search here
        // 5. Determine response type
        boolean isAjax = true;
        
        bh.consume(searchTerm);
        bh.consume(isAjax);
    }

    /**
     * Benchmark: Complete Login check flow.
     * Authentication verification pattern.
     */
    @Benchmark
    public void completeLoginCheckFlow(Blackhole bh) {
        // 1. Get credentials
        String username = requestParams.get("username");
        String password = requestParams.get("password");
        
        // 2. Validate presence
        boolean valid = username != null && !username.isEmpty()
                     && password != null && !password.isEmpty();
        
        // 3. Would authenticate here
        boolean authenticated = valid; // Simulated
        
        // 4. Determine response
        String result;
        if (!valid) {
            result = "error:invalid_input";
        } else if (!authenticated) {
            result = "error:auth_failed";
        } else {
            result = "success";
        }
        
        bh.consume(result);
    }

    /**
     * Main method to run benchmarks standalone.
     */
    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(ControllerBenchmark.class.getSimpleName())
                .forks(1)
                .warmupIterations(2)
                .measurementIterations(3)
                .build();

        new Runner(opt).run();
    }
}
