/**
 * Controller/Servlet Unit Tests Package
 * 
 * Testing Level: Unit
 * Technique: White-Box (Statement Coverage, Branch Coverage, Loop Boundary Testing)
 * 
 * ============================================================================
 * CONTROLLER BRANCH STRUCTURE ANALYSIS SUMMARY (Step 3.1)
 * ============================================================================
 * 
 * This package contains unit tests for the control layer (servlets/controllers).
 * All controllers follow the HttpServlet pattern with doGet() and doPost() methods.
 * 
 * Common Patterns Identified:
 * -----------------------------------------------------------------
 * 1. Try-Catch blocks for SQLException handling (all database operations)
 * 2. Session validation (user authentication checks)
 * 3. AJAX request detection (X-Requested-With header)
 * 4. Parameter validation (null/empty checks)
 * 5. Authorization checks (admin vs regular user)
 * 
 * Controller Coverage Summary:
 * -----------------------------------------------------------------
 * | Controller      | Branches | Loops | Key Conditions                    |
 * |-----------------|----------|-------|-----------------------------------|
 * | Home            | 2        | 0     | SQLException handling             |
 * | Login           | 8        | 0     | User exists, password match, AJAX |
 * | Cart            | 12+      | 1+    | Action switch, session, quantity  |
 * | Register        | 8+       | 0     | Validation, duplicate user, AJAX  |
 * | Search          | 4+       | 1+    | Query validation, results loop    |
 * | Checkout        | 10+      | 1+    | Cart validation, order creation   |
 * | ProductDetails  | 4+       | 0     | Product exists, SQLException      |
 * | ProductAdmin    | 4+       | 1+    | Admin check, product listing      |
 * | ProductEdit     | 8+       | 0     | Admin, product exists, validation |
 * | ProductUpload   | 8+       | 0     | Admin, validation, file upload    |
 * | Orders          | 4+       | 1+    | User session, order listing       |
 * | Addresses       | 8+       | 1+    | CRUD operations, validation       |
 * | AccountManage   | 6+       | 1+    | Admin check, user operations      |
 * | UserProfile     | 6+       | 0     | Session, update validation        |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets (per SPEC.md):
 * - TER1 (Statement Coverage): ≥ 80%
 * - TER2 (Branch Coverage): ≥ 70%
 * 
 * Testing Strategy:
 * - Use Mockito to mock HttpServletRequest, HttpServletResponse, HttpSession
 * - Use Mockito to mock DAO interfaces (IProductDao, IUserDao, etc.)
 * - Verify interactions with mocked objects
 * - Test both success and exception paths
 * 
 * @see control.Home
 * @see control.Login
 * @see control.Cart
 * @see control.Register
 * @see control.Search
 * @see control.Checkout
 * @see control.ProductDetails
 * @see control.ProductAdmin
 * @see control.ProductEdit
 * @see control.ProductUpload
 * @see control.Orders
 * @see control.Addresses
 * @see control.AccountManage
 * @see control.UserProfile
 */
package control;
