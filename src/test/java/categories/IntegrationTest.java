package categories;

import org.junit.jupiter.api.Tag;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Marker annotation for integration tests.
 * 
 * <p>Integration tests verify component interactions and may use external resources
 * like databases. They are slower than unit tests and run during the verify phase.</p>
 * 
 * <h2>Characteristics</h2>
 * <ul>
 *   <li>May use H2 in-memory database</li>
 *   <li>Tests real component interactions</li>
 *   <li>Execution time: 100ms - 5s per test</li>
 * </ul>
 * 
 * <h2>Usage</h2>
 * <pre>
 * {@code @IntegrationTest}
 * class MyIntegrationTest {
 *     // test methods
 * }
 * </pre>
 * 
 * <h2>Execution</h2>
 * <ul>
 *   <li>Run only integration tests: {@code mvn test -Dgroups=integration}</li>
 *   <li>Run all tests: {@code mvn verify}</li>
 *   <li>Skip integration tests: {@code mvn test -DexcludedGroups=integration}</li>
 * </ul>
 * 
 * @see UnitTest
 */
@Target({ElementType.TYPE, ElementType.METHOD})
@Retention(RetentionPolicy.RUNTIME)
@Tag("integration")
public @interface IntegrationTest {
}
