package categories;

import org.junit.jupiter.api.Tag;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Marker annotation for unit tests.
 * 
 * <p>Unit tests are fast tests that run in isolation without external dependencies.
 * They should complete in milliseconds and run on every commit/PR.</p>
 * 
 * <h2>Characteristics</h2>
 * <ul>
 *   <li>No database access (mocked DAOs)</li>
 *   <li>No file system access</li>
 *   <li>No network calls</li>
 *   <li>Execution time: &lt; 100ms per test</li>
 * </ul>
 * 
 * <h2>Usage</h2>
 * <pre>
 * {@code @UnitTest}
 * class MyClassTest {
 *     // test methods
 * }
 * </pre>
 * 
 * <h2>Execution</h2>
 * <ul>
 *   <li>Run only unit tests: {@code mvn test -Dgroups=unit}</li>
 *   <li>Run all tests: {@code mvn verify}</li>
 * </ul>
 * 
 * @see IntegrationTest
 */
@Target({ElementType.TYPE, ElementType.METHOD})
@Retention(RetentionPolicy.RUNTIME)
@Tag("unit")
public @interface UnitTest {
}
