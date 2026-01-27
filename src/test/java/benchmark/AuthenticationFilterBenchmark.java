package benchmark;

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
 * JMH Microbenchmarks for AuthenticationFilter logic.
 * 
 * <p>The AuthenticationFilter is extremely performance-critical because:</p>
 * <ul>
 *   <li>Executes on EVERY HTTP request</li>
 *   <li>Contains multiple conditional checks per request</li>
 *   <li>Session attribute lookups</li>
 *   <li>String comparisons and URL pattern matching</li>
 *   <li>Admin role verification for protected paths</li>
 * </ul>
 * 
 * <p>These benchmarks test the core filter logic without servlet overhead.</p>
 */
@BenchmarkMode({Mode.AverageTime, Mode.Throughput})
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Thread)
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 2, jvmArgs = {"-Xms128M", "-Xmx128M"})
public class AuthenticationFilterBenchmark {

    // Simulated session storage
    private Map<String, Object> session;
    private UserBean regularUser;
    private UserBean adminUser;
    
    // Test URIs
    private String loginUri;
    private String homeUri;
    private String cartUri;
    private String adminUri;
    private String loginPageUri;
    private String staticCssUri;
    private String staticJsUri;
    private String productUri;
    
    // Context path
    private String contextPath;

    @Setup(Level.Trial)
    public void setUp() {
        contextPath = "/shapedibles";
        
        // Test URIs
        loginUri = contextPath + "/Login";
        homeUri = contextPath + "/Home";
        cartUri = contextPath + "/Cart";
        adminUri = contextPath + "/admin/ProductAdmin";
        loginPageUri = contextPath + "/WEB-INF/jsp/loginView.jsp";
        staticCssUri = contextPath + "/css/style.css";
        staticJsUri = contextPath + "/js/main.js";
        productUri = contextPath + "/ProductDetails";
        
        // Create users
        regularUser = new UserBean();
        regularUser.setUsername("testuser");
        regularUser.setUserAdmin(0);
        
        adminUser = new UserBean();
        adminUser.setUsername("admin");
        adminUser.setUserAdmin(1);
        
        // Initialize session
        session = new HashMap<>();
    }

    @Setup(Level.Invocation)
    public void resetSession() {
        session.clear();
    }

    // ==================== LOGIN CHECK OPERATIONS ====================

    /**
     * Benchmark: Check if user is logged in (session with user).
     * Tests session attribute lookup with existing user.
     */
    @Benchmark
    public void checkLoggedInUser(Blackhole bh) {
        session.put("LoggedUser", regularUser);
        boolean isLoggedIn = session.get("LoggedUser") != null;
        bh.consume(isLoggedIn);
    }

    /**
     * Benchmark: Check if user is not logged in (no session).
     * Tests null check performance.
     */
    @Benchmark
    public void checkNotLoggedIn(Blackhole bh) {
        boolean isLoggedIn = session.get("LoggedUser") != null;
        bh.consume(isLoggedIn);
    }

    // ==================== URI MATCHING OPERATIONS ====================

    /**
     * Benchmark: Check if request is for login URI.
     * Tests String.equals() performance.
     */
    @Benchmark
    public void checkLoginUri(Blackhole bh) {
        String requestUri = loginUri;
        boolean isLoginRequest = requestUri.equals(loginUri);
        bh.consume(isLoginRequest);
    }

    /**
     * Benchmark: Check if request is for login page JSP.
     * Tests String.endsWith() performance.
     */
    @Benchmark
    public void checkLoginPageUri(Blackhole bh) {
        String requestUri = loginPageUri;
        boolean isLoginPage = requestUri.endsWith("loginView.jsp");
        bh.consume(isLoginPage);
    }

    /**
     * Benchmark: Check if request is for admin area.
     * Tests String.contains() performance.
     */
    @Benchmark
    public void checkAdminUri(Blackhole bh) {
        String requestUri = adminUri;
        boolean isAdmin = requestUri.contains("/admin/");
        bh.consume(isAdmin);
    }

    /**
     * Benchmark: Check non-admin URI for admin pattern.
     * Tests String.contains() for non-matching case.
     */
    @Benchmark
    public void checkNonAdminUri(Blackhole bh) {
        String requestUri = cartUri;
        boolean isAdmin = requestUri.contains("/admin/");
        bh.consume(isAdmin);
    }

    // ==================== ADMIN ROLE CHECK ====================

    /**
     * Benchmark: Admin role verification for admin user.
     * Tests user bean retrieval and admin flag check.
     */
    @Benchmark
    public void checkAdminRoleForAdmin(Blackhole bh) {
        session.put("LoggedUser", adminUser);
        UserBean user = (UserBean) session.get("LoggedUser");
        boolean isAdmin = user.getUserAdmin() == 1;
        bh.consume(isAdmin);
    }

    /**
     * Benchmark: Admin role verification for regular user.
     * Tests user bean retrieval and admin flag check (failing case).
     */
    @Benchmark
    public void checkAdminRoleForRegularUser(Blackhole bh) {
        session.put("LoggedUser", regularUser);
        UserBean user = (UserBean) session.get("LoggedUser");
        boolean isAdmin = user.getUserAdmin() == 1;
        bh.consume(isAdmin);
    }

    // ==================== FULL FILTER DECISION LOGIC ====================

    /**
     * Benchmark: Full filter logic - logged in user accessing regular page.
     * Most common case for authenticated users.
     */
    @Benchmark
    public void filterLogicLoggedInRegularPage(Blackhole bh) {
        session.put("LoggedUser", regularUser);
        String requestUri = cartUri;
        
        boolean isLoggedIn = session.get("LoggedUser") != null;
        boolean isLoginRequest = requestUri.equals(loginUri);
        boolean isLoginPage = requestUri.endsWith("loginView.jsp");
        
        boolean shouldProceed = false;
        if (isLoggedIn || isLoginRequest || isLoginPage) {
            if (isLoggedIn && requestUri.contains("/admin/")) {
                UserBean user = (UserBean) session.get("LoggedUser");
                shouldProceed = user.getUserAdmin() == 1;
            } else {
                shouldProceed = true;
            }
        }
        
        bh.consume(shouldProceed);
    }

    /**
     * Benchmark: Full filter logic - anonymous user accessing login.
     * Common case for unauthenticated users.
     */
    @Benchmark
    public void filterLogicAnonymousLoginPage(Blackhole bh) {
        String requestUri = loginUri;
        
        boolean isLoggedIn = session.get("LoggedUser") != null;
        boolean isLoginRequest = requestUri.equals(loginUri);
        boolean isLoginPage = requestUri.endsWith("loginView.jsp");
        
        boolean shouldProceed = isLoggedIn || isLoginRequest || isLoginPage;
        
        bh.consume(shouldProceed);
    }

    /**
     * Benchmark: Full filter logic - admin user accessing admin page.
     * Tests the complete admin verification path.
     */
    @Benchmark
    public void filterLogicAdminAccessingAdminPage(Blackhole bh) {
        session.put("LoggedUser", adminUser);
        String requestUri = adminUri;
        
        boolean isLoggedIn = session.get("LoggedUser") != null;
        boolean isLoginRequest = requestUri.equals(loginUri);
        boolean isLoginPage = requestUri.endsWith("loginView.jsp");
        
        boolean shouldProceed = false;
        if (isLoggedIn || isLoginRequest || isLoginPage) {
            if (isLoggedIn && requestUri.contains("/admin/")) {
                UserBean user = (UserBean) session.get("LoggedUser");
                shouldProceed = user.getUserAdmin() == 1;
            } else {
                shouldProceed = true;
            }
        }
        
        bh.consume(shouldProceed);
    }

    /**
     * Benchmark: Full filter logic - regular user trying to access admin.
     * Tests the rejection path for unauthorized access.
     */
    @Benchmark
    public void filterLogicRegularUserAccessingAdminPage(Blackhole bh) {
        session.put("LoggedUser", regularUser);
        String requestUri = adminUri;
        
        boolean isLoggedIn = session.get("LoggedUser") != null;
        boolean isLoginRequest = requestUri.equals(loginUri);
        boolean isLoginPage = requestUri.endsWith("loginView.jsp");
        
        boolean shouldProceed = false;
        boolean shouldRedirect = false;
        
        if (isLoggedIn || isLoginRequest || isLoginPage) {
            if (isLoggedIn && requestUri.contains("/admin/")) {
                UserBean user = (UserBean) session.get("LoggedUser");
                if (user.getUserAdmin() != 1) {
                    shouldRedirect = true;
                } else {
                    shouldProceed = true;
                }
            } else {
                shouldProceed = true;
            }
        }
        
        bh.consume(shouldProceed);
        bh.consume(shouldRedirect);
    }

    /**
     * Benchmark: Full filter logic - anonymous accessing protected page.
     * Tests the redirect-to-login path.
     */
    @Benchmark
    public void filterLogicAnonymousAccessingProtectedPage(Blackhole bh) {
        String requestUri = cartUri;
        
        boolean isLoggedIn = session.get("LoggedUser") != null;
        boolean isLoginRequest = requestUri.equals(loginUri);
        boolean isLoginPage = requestUri.endsWith("loginView.jsp");
        
        boolean shouldProceed = isLoggedIn || isLoginRequest || isLoginPage;
        boolean shouldRedirect = !shouldProceed;
        
        if (shouldRedirect) {
            // Simulate storing redirect URL
            session.put("redirectURL", requestUri);
        }
        
        bh.consume(shouldProceed);
        bh.consume(shouldRedirect);
    }

    // ==================== STRING OPERATIONS ====================

    /**
     * Benchmark: Context path concatenation.
     * Tests string concatenation overhead.
     */
    @Benchmark
    public void contextPathConcatenation(Blackhole bh) {
        String fullPath = contextPath + "/Login";
        bh.consume(fullPath);
    }

    /**
     * Benchmark: Multiple string operations (typical filter path).
     * Tests combined equals, endsWith, contains operations.
     */
    @Benchmark
    public void multipleStringOperations(Blackhole bh) {
        String requestUri = cartUri;
        
        boolean a = requestUri.equals(loginUri);
        boolean b = requestUri.endsWith("loginView.jsp");
        boolean c = requestUri.contains("/admin/");
        boolean d = requestUri.startsWith(contextPath);
        
        bh.consume(a);
        bh.consume(b);
        bh.consume(c);
        bh.consume(d);
    }

    /**
     * Main method to run benchmarks standalone.
     */
    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(AuthenticationFilterBenchmark.class.getSimpleName())
                .forks(1)
                .warmupIterations(3)
                .measurementIterations(5)
                .build();

        new Runner(opt).run();
    }
}
