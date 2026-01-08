/**
 * Test categorization annotations for regression testing strategy.
 * 
 * <h2>Purpose</h2>
 * <p>Per SPEC.md Execution Strategy, tests are categorized to support:</p>
 * <ul>
 *   <li><b>Every commit/PR:</b> Fast unit tests (≤ 5 min total)</li>
 *   <li><b>Daily/Nightly:</b> Full test suite including integration tests</li>
 *   <li><b>Pre-release:</b> Full suite with any system/non-functional tests</li>
 * </ul>
 * 
 * <h2>Available Annotations</h2>
 * <table border="1">
 *   <tr>
 *     <th>Annotation</th>
 *     <th>Tag</th>
 *     <th>Run Frequency</th>
 *     <th>Command</th>
 *   </tr>
 *   <tr>
 *     <td>{@link UnitTest}</td>
 *     <td>unit</td>
 *     <td>Every commit</td>
 *     <td>{@code mvn test -Dgroups=unit}</td>
 *   </tr>
 *   <tr>
 *     <td>{@link IntegrationTest}</td>
 *     <td>integration</td>
 *     <td>Daily/Pre-release</td>
 *     <td>{@code mvn test -Dgroups=integration}</td>
 *   </tr>
 * </table>
 * 
 * <h2>Maven Commands</h2>
 * <ul>
 *   <li>{@code mvn test} - Runs all tests (unit + integration)</li>
 *   <li>{@code mvn test -Dgroups=unit} - Runs only unit tests (fast)</li>
 *   <li>{@code mvn test -Dgroups=integration} - Runs only integration tests</li>
 *   <li>{@code mvn test -DexcludedGroups=integration} - Runs all except integration</li>
 *   <li>{@code mvn verify} - Runs all tests with coverage report</li>
 * </ul>
 * 
 * <h2>CI/CD Integration</h2>
 * <p>The GitHub workflow should be configured to:</p>
 * <ol>
 *   <li>Run {@code mvn test -DexcludedGroups=integration} on every PR (fast feedback)</li>
 *   <li>Run {@code mvn verify} on merge to main (full validation)</li>
 * </ol>
 * 
 * @see categories.UnitTest
 * @see categories.IntegrationTest
 */
package categories;
