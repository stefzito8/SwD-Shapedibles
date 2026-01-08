/**
 * Integration tests for SwD-Shapedibles application.
 * 
 * <h2>Integration Testing Strategy: Modified Sandwich</h2>
 * 
 * <p>Per the course tutorial:</p>
 * <blockquote>
 * "Modified Sandwich: Inspired by Sandwich but includes unit testing of middle components.
 * All components are first individually tested."
 * </blockquote>
 * 
 * <h3>Strategy Justification</h3>
 * <p>Modified Sandwich is chosen because:</p>
 * <ol>
 *   <li><b>Unit tests completed:</b> All model, controller, and filter layers have been unit tested (Phases 2-4)</li>
 *   <li><b>Middle layer focus:</b> Controllers integrate with both Model (lower) and Filter/Web (upper)</li>
 *   <li><b>Minimal stubs/drivers:</b> Only HTTP request/response simulation needed as driver</li>
 *   <li><b>Parallel testing:</b> Database layer (bottom-up) and Controller-Model (top-down from controller) can proceed in parallel</li>
 * </ol>
 * 
 * <h3>Integration Points Summary</h3>
 * 
 * <table border="1">
 *   <tr>
 *     <th>Integration Point</th>
 *     <th>Components</th>
 *     <th>Strategy</th>
 *     <th>Priority</th>
 *     <th>Test Class</th>
 *   </tr>
 *   <tr>
 *     <td>Controller ↔ DAO</td>
 *     <td>14 controllers × 8 DAOs</td>
 *     <td>Modified Sandwich</td>
 *     <td>HIGH</td>
 *     <td>{@link ControllerModelIntegrationTest}</td>
 *   </tr>
 *   <tr>
 *     <td>DAO ↔ Database</td>
 *     <td>8 DAOs × H2 database</td>
 *     <td>Bottom-Up</td>
 *     <td>HIGH</td>
 *     <td>{@link DatabaseIntegrationTest}</td>
 *   </tr>
 *   <tr>
 *     <td>Filter ↔ Controller</td>
 *     <td>AuthenticationFilter × Protected controllers</td>
 *     <td>Top-Down</td>
 *     <td>MEDIUM</td>
 *     <td>(Future: FilterChainIntegrationTest)</td>
 *   </tr>
 *   <tr>
 *     <td>Bean ↔ DAO</td>
 *     <td>7 Beans × 8 DAOs</td>
 *     <td>Bottom-Up</td>
 *     <td>MEDIUM</td>
 *     <td>{@link DatabaseIntegrationTest}</td>
 *   </tr>
 * </table>
 * 
 * <h3>High-Priority Integration Flows</h3>
 * 
 * <h4>1. Product Display Flow (Home page)</h4>
 * <pre>
 * Home Controller
 *      ↓ calls
 * ProductDaoDataSource.doRetrieveAll()
 *      ↓ for each product
 * InfoDaoDataSource.doRetrieveByProduct()
 *      ↓ joins with
 * NutritionTableDaoDataSource.doRetrieveByProduct()
 *      ↓ returns
 * List&lt;ProductBean&gt; with InfoBean and NutritionTableBean
 * </pre>
 * 
 * <h4>2. Authentication Flow (Login)</h4>
 * <pre>
 * Login Controller
 *      ↓ receives username/password
 * UserDaoDataSource.doRetrieveByUsername()
 *      ↓ returns
 * UserBean (with hashed password)
 *      ↓ controller verifies
 * Password hash match → Session creation
 * </pre>
 * 
 * <h4>3. E-commerce Flow (Cart → Checkout)</h4>
 * <pre>
 * Cart Controller
 *      ↓ manages
 * ContainDaoDataSource (cart items)
 *      ↓ references
 * ProductDaoDataSource (product details)
 *      ↓
 * Checkout Controller
 *      ↓ creates
 * OrderDaoDataSource.doSave()
 *      ↓ with
 * AddressDaoDataSource (shipping address)
 * </pre>
 * 
 * <h3>Test Environment</h3>
 * <ul>
 *   <li><b>Database:</b> H2 in-memory (replaces SQLite for testing)</li>
 *   <li><b>Driver:</b> Test class simulates HTTP request/response</li>
 *   <li><b>Stubs:</b> None - real DAO implementations used</li>
 *   <li><b>Isolation:</b> Each test starts with clean database state</li>
 * </ul>
 * 
 * <h3>References</h3>
 * <ul>
 *   <li>SPEC.md: Integration Testing section (REQ-INT-01 through REQ-INT-03)</li>
 *   <li>Tutorial: "Integration Test Case Selection" section</li>
 *   <li>pom.xml: H2 database dependency for testing</li>
 * </ul>
 * 
 * @see ControllerModelIntegrationTest
 * @see DatabaseIntegrationTest
 */
package integration;