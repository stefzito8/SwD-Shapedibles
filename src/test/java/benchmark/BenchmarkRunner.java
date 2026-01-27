package benchmark;

import org.openjdk.jmh.results.format.ResultFormatType;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;
import org.openjdk.jmh.runner.options.TimeValue;

import java.io.File;
import java.text.SimpleDateFormat;
import java.util.Date;

/**
 * JMH Benchmark Runner for SwD-Shapedibles performance testing.
 * 
 * <p>This runner executes all benchmarks and generates comprehensive reports.
 * It can be run in different modes:</p>
 * <ul>
 *   <li><b>Full</b>: Complete benchmark suite with high accuracy (slow)</li>
 *   <li><b>Quick</b>: Reduced iterations for development/CI (fast)</li>
 *   <li><b>Specific</b>: Run specific benchmark class</li>
 * </ul>
 * 
 * <h2>Benchmark Categories:</h2>
 * <ol>
 *   <li><b>CartBenchmark</b>: Shopping cart operations (add/delete/query)</li>
 *   <li><b>AuthenticationFilterBenchmark</b>: Per-request filter logic</li>
 *   <li><b>DataSourceBenchmark</b>: Database operations with H2</li>
 *   <li><b>ModelBeanBenchmark</b>: Bean instantiation and access patterns</li>
 * </ol>
 * 
 * <h2>Usage:</h2>
 * <pre>
 * // Run from Maven:
 * mvn test -Dtest=BenchmarkRunner
 * 
 * // Run quick mode:
 * mvn test -Dtest=BenchmarkRunner -Dbenchmark.mode=quick
 * 
 * // Run specific benchmark:
 * mvn test -Dtest=BenchmarkRunner -Dbenchmark.include=CartBenchmark
 * </pre>
 */
public class BenchmarkRunner {

    private static final String RESULT_DIR = "target/jmh-results";

    /**
     * Run all benchmarks with configurable options.
     */
    public static void main(String[] args) throws RunnerException {
        // Create result directory
        new File(RESULT_DIR).mkdirs();
        
        // Determine mode from system property
        String mode = System.getProperty("benchmark.mode", "quick");
        String include = System.getProperty("benchmark.include", ".*Benchmark");
        
        Options opt;
        
        switch (mode.toLowerCase()) {
            case "full":
                opt = buildFullOptions(include);
                break;
            case "specific":
                opt = buildSpecificOptions(include);
                break;
            case "quick":
            default:
                opt = buildQuickOptions(include);
                break;
        }
        
        System.out.println("=".repeat(60));
        System.out.println("SwD-Shapedibles JMH Benchmark Suite");
        System.out.println("=".repeat(60));
        System.out.println("Mode: " + mode.toUpperCase());
        System.out.println("Include pattern: " + include);
        System.out.println("Results directory: " + RESULT_DIR);
        System.out.println("=".repeat(60));
        
        new Runner(opt).run();
        
        System.out.println("\n" + "=".repeat(60));
        System.out.println("Benchmark completed! Results saved to: " + RESULT_DIR);
        System.out.println("=".repeat(60));
    }

    /**
     * Build options for quick development runs.
     * Fewer iterations, single fork for faster feedback.
     */
    private static Options buildQuickOptions(String include) {
        String timestamp = new SimpleDateFormat("yyyyMMdd-HHmmss").format(new Date());
        
        return new OptionsBuilder()
                .include(include)
                // Minimal warmup and measurement for quick feedback
                .warmupIterations(1)
                .warmupTime(TimeValue.milliseconds(500))
                .measurementIterations(2)
                .measurementTime(TimeValue.milliseconds(500))
                // Single fork to reduce total time
                .forks(1)
                // JVM settings
                .jvmArgs("-Xms128M", "-Xmx256M")
                // Output settings
                .result(RESULT_DIR + "/benchmark-results-quick-" + timestamp + ".json")
                .resultFormat(ResultFormatType.JSON)
                // Fail on error
                .shouldFailOnError(true)
                // Sync iterations for consistent results
                .syncIterations(true)
                .build();
    }

    /**
     * Build options for full production runs.
     * Many iterations, multiple forks for statistical significance.
     */
    private static Options buildFullOptions(String include) {
        String timestamp = new SimpleDateFormat("yyyyMMdd-HHmmss").format(new Date());
        
        return new OptionsBuilder()
                .include(include)
                // Thorough warmup
                .warmupIterations(5)
                .warmupTime(TimeValue.seconds(1))
                // Many measurements for accuracy
                .measurementIterations(10)
                .measurementTime(TimeValue.seconds(1))
                // Multiple forks for variance analysis
                .forks(3)
                // Production JVM settings
                .jvmArgs("-Xms256M", "-Xmx512M", "-XX:+UseG1GC")
                // Output settings
                .result(RESULT_DIR + "/benchmark-results-full-" + timestamp + ".json")
                .resultFormat(ResultFormatType.JSON)
                // Fail on error
                .shouldFailOnError(true)
                // Sync iterations
                .syncIterations(true)
                .build();
    }

    /**
     * Build options for specific benchmark class.
     * Moderate iterations for focused testing.
     */
    private static Options buildSpecificOptions(String include) {
        String timestamp = new SimpleDateFormat("yyyyMMdd-HHmmss").format(new Date());
        
        return new OptionsBuilder()
                .include(include)
                // Moderate warmup
                .warmupIterations(3)
                .warmupTime(TimeValue.milliseconds(800))
                // Moderate measurements
                .measurementIterations(5)
                .measurementTime(TimeValue.milliseconds(800))
                // Two forks for some variance data
                .forks(2)
                // JVM settings
                .jvmArgs("-Xms256M", "-Xmx256M")
                // Output settings
                .result(RESULT_DIR + "/benchmark-results-specific-" + timestamp + ".json")
                .resultFormat(ResultFormatType.JSON)
                // Fail on error
                .shouldFailOnError(true)
                // Sync iterations
                .syncIterations(true)
                .build();
    }

    /**
     * JUnit-compatible test entry point.
     * Allows running benchmarks via Maven Surefire.
     */
    @org.junit.jupiter.api.Test
    public void runBenchmarks() throws RunnerException {
        main(new String[]{});
    }
}
