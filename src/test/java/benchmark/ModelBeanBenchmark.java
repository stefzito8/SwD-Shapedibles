package benchmark;

import model.bean.*;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

/**
 * JMH Microbenchmarks for Model Bean operations.
 * 
 * <p>Model beans are performance-critical because:</p>
 * <ul>
 *   <li>High instantiation frequency during database operations</li>
 *   <li>Object creation contributes to GC pressure</li>
 *   <li>Getter/setter calls are frequent in JSP/template rendering</li>
 *   <li>hashCode/equals impact HashMap performance (Cart uses ProductBean as key)</li>
 *   <li>Serialization overhead for session storage</li>
 * </ul>
 * 
 * <p>These benchmarks test object lifecycle and access patterns.</p>
 */
@BenchmarkMode({Mode.AverageTime, Mode.Throughput})
@OutputTimeUnit(TimeUnit.NANOSECONDS)
@State(Scope.Thread)
@Warmup(iterations = 3, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Fork(value = 2, jvmArgs = {"-Xms256M", "-Xmx256M"})
public class ModelBeanBenchmark {

    private ProductBean existingProduct;
    private InfoBean existingInfo;
    private UserBean existingUser;
    private NutritionTableBean existingNutrition;
    private ImageBean existingImage;
    private List<ImageBean> imageList;
    
    @Param({"10", "50", "100"})
    private int bulkSize;

    @Setup(Level.Trial)
    public void setUp() {
        // Pre-create beans for read benchmarks
        existingProduct = new ProductBean();
        existingProduct.setCodice(1);
        existingProduct.setNome("Test Product");
        existingProduct.setInfoCorrenti(100);
        
        existingInfo = new InfoBean();
        existingInfo.setCodice(1);
        existingInfo.setNome("Test Info");
        existingInfo.setCosto(29.99);
        existingInfo.setDescrizione("A detailed description of the product");
        existingInfo.setDisponibilità(1);
        existingInfo.setTipologia("Protein");
        
        existingUser = new UserBean();
        existingUser.setUsername("testuser");
        existingUser.setEmail("test@example.com");
        existingUser.setPass("hashedpassword123");
        existingUser.setNomeCognome("Test User");
        existingUser.setSesso("M");
        existingUser.setPaese("Italy");
        existingUser.setDataNascita("1990-01-01");
        existingUser.setUserAdmin(0);
        
        existingNutrition = new NutritionTableBean();
        existingNutrition.setCodiceProdotto(1);
        existingNutrition.setEnergia(250);
        existingNutrition.setGrassi(5.5);
        existingNutrition.setGrassiSaturi(1.2);
        existingNutrition.setCarboedrati(30.0);
        existingNutrition.setZucherri(5.0);
        existingNutrition.setFibre(3.0);
        existingNutrition.setProteine(25.0);
        existingNutrition.setSale(0.5);
        
        existingImage = new ImageBean();
        existingImage.setNumImage(1);
        existingImage.setCodiceProdotto(1);
        existingImage.setImg("product_1_square.jpg");
        
        // Create image list for product
        imageList = new ArrayList<>();
        for (int i = 1; i <= 5; i++) {
            ImageBean img = new ImageBean();
            img.setNumImage(i);
            img.setCodiceProdotto(1);
            img.setImg("product_1_img" + i + ".jpg");
            imageList.add(img);
        }
        existingProduct.setImages(imageList);
    }

    // ==================== INSTANTIATION BENCHMARKS ====================

    /**
     * Benchmark: ProductBean instantiation.
     * Tests constructor and default initialization.
     */
    @Benchmark
    public void productBeanInstantiation(Blackhole bh) {
        ProductBean bean = new ProductBean();
        bh.consume(bean);
    }

    /**
     * Benchmark: InfoBean instantiation.
     * Tests constructor with more fields.
     */
    @Benchmark
    public void infoBeanInstantiation(Blackhole bh) {
        InfoBean bean = new InfoBean();
        bh.consume(bean);
    }

    /**
     * Benchmark: UserBean instantiation.
     * Tests constructor with many string fields.
     */
    @Benchmark
    public void userBeanInstantiation(Blackhole bh) {
        UserBean bean = new UserBean();
        bh.consume(bean);
    }

    /**
     * Benchmark: NutritionTableBean instantiation.
     * Tests constructor with numeric fields.
     */
    @Benchmark
    public void nutritionTableBeanInstantiation(Blackhole bh) {
        NutritionTableBean bean = new NutritionTableBean();
        bh.consume(bean);
    }

    /**
     * Benchmark: ImageBean instantiation.
     * Tests simple constructor.
     */
    @Benchmark
    public void imageBeanInstantiation(Blackhole bh) {
        ImageBean bean = new ImageBean();
        bh.consume(bean);
    }

    // ==================== BULK INSTANTIATION BENCHMARKS ====================

    /**
     * Benchmark: Bulk ProductBean creation.
     * Simulates database result set processing.
     */
    @Benchmark
    public void bulkProductBeanCreation(Blackhole bh) {
        List<ProductBean> products = new ArrayList<>(bulkSize);
        for (int i = 0; i < bulkSize; i++) {
            ProductBean bean = new ProductBean();
            bean.setCodice(i);
            bean.setNome("Product " + i);
            bean.setInfoCorrenti(i * 10);
            products.add(bean);
        }
        bh.consume(products);
    }

    /**
     * Benchmark: Bulk InfoBean creation with all fields.
     * Simulates complete data mapping.
     */
    @Benchmark
    public void bulkInfoBeanCreation(Blackhole bh) {
        List<InfoBean> infos = new ArrayList<>(bulkSize);
        for (int i = 0; i < bulkSize; i++) {
            InfoBean bean = new InfoBean();
            bean.setCodice(i);
            bean.setNome("Info " + i);
            bean.setCosto(19.99 + i);
            bean.setDescrizione("Description for product " + i);
            bean.setDisponibilità(i % 2);
            bean.setTipologia("Type" + (i % 5));
            infos.add(bean);
        }
        bh.consume(infos);
    }

    // ==================== GETTER BENCHMARKS ====================

    /**
     * Benchmark: ProductBean getter chain.
     * Simulates JSP template access pattern.
     */
    @Benchmark
    public void productBeanGetters(Blackhole bh) {
        bh.consume(existingProduct.getCodice());
        bh.consume(existingProduct.getNome());
        bh.consume(existingProduct.getInfoCorrenti());
        bh.consume(existingProduct.getImages());
    }

    /**
     * Benchmark: InfoBean getter chain.
     * Tests all getters in sequence.
     */
    @Benchmark
    public void infoBeanGetters(Blackhole bh) {
        bh.consume(existingInfo.getCodice());
        bh.consume(existingInfo.getNome());
        bh.consume(existingInfo.getCosto());
        bh.consume(existingInfo.getDescrizione());
        bh.consume(existingInfo.getDisponibilità());
        bh.consume(existingInfo.getTipologia());
    }

    /**
     * Benchmark: UserBean getter chain.
     * Tests string field access.
     */
    @Benchmark
    public void userBeanGetters(Blackhole bh) {
        bh.consume(existingUser.getUsername());
        bh.consume(existingUser.getEmail());
        bh.consume(existingUser.getPass());
        bh.consume(existingUser.getNomeCognome());
        bh.consume(existingUser.getSesso());
        bh.consume(existingUser.getPaese());
        bh.consume(existingUser.getDataNascita());
        bh.consume(existingUser.getUserAdmin());
    }

    /**
     * Benchmark: NutritionTableBean getter chain.
     * Tests numeric field access (int and double).
     */
    @Benchmark
    public void nutritionBeanGetters(Blackhole bh) {
        bh.consume(existingNutrition.getCodiceProdotto());
        bh.consume(existingNutrition.getEnergia());
        bh.consume(existingNutrition.getGrassi());
        bh.consume(existingNutrition.getGrassiSaturi());
        bh.consume(existingNutrition.getCarboedrati());
        bh.consume(existingNutrition.getZucherri());
        bh.consume(existingNutrition.getFibre());
        bh.consume(existingNutrition.getProteine());
        bh.consume(existingNutrition.getSale());
    }

    // ==================== SETTER BENCHMARKS ====================

    /**
     * Benchmark: ProductBean setter chain.
     * Simulates database result mapping.
     */
    @Benchmark
    public void productBeanSetters(Blackhole bh) {
        ProductBean bean = new ProductBean();
        bean.setCodice(1);
        bean.setNome("Test");
        bean.setInfoCorrenti(100);
        bean.setImages(imageList);
        bh.consume(bean);
    }

    /**
     * Benchmark: Complete InfoBean population.
     * Tests all setters in sequence.
     */
    @Benchmark
    public void infoBeanSetters(Blackhole bh) {
        InfoBean bean = new InfoBean();
        bean.setCodice(1);
        bean.setNome("Test");
        bean.setCosto(29.99);
        bean.setDescrizione("Test description");
        bean.setDisponibilità(1);
        bean.setTipologia("TestType");
        bh.consume(bean);
    }

    // ==================== HASH/EQUALS BENCHMARKS ====================

    /**
     * Benchmark: ProductBean hashCode.
     * Critical for HashMap performance in Cart.
     */
    @Benchmark
    public void productBeanHashCode(Blackhole bh) {
        int hash = existingProduct.hashCode();
        bh.consume(hash);
    }

    /**
     * Benchmark: ProductBean equals - same object.
     * Tests identity comparison path.
     */
    @Benchmark
    public void productBeanEqualsSameObject(Blackhole bh) {
        boolean equals = existingProduct.equals(existingProduct);
        bh.consume(equals);
    }

    /**
     * Benchmark: ProductBean equals - equal objects.
     * Tests full equality comparison.
     */
    @Benchmark
    public void productBeanEqualsEqualObjects(Blackhole bh) {
        ProductBean other = new ProductBean();
        other.setCodice(1);
        boolean equals = existingProduct.equals(other);
        bh.consume(equals);
    }

    /**
     * Benchmark: ProductBean equals - different objects.
     * Tests full comparison with different values.
     */
    @Benchmark
    public void productBeanEqualsDifferentObjects(Blackhole bh) {
        ProductBean other = new ProductBean();
        other.setCodice(999);
        boolean equals = existingProduct.equals(other);
        bh.consume(equals);
    }

    /**
     * Benchmark: ProductBean equals - null check.
     * Tests null comparison path.
     */
    @Benchmark
    public void productBeanEqualsNull(Blackhole bh) {
        boolean equals = existingProduct.equals(null);
        bh.consume(equals);
    }

    // ==================== STRING OPERATIONS ====================

    /**
     * Benchmark: InfoBean toString.
     * Tests string concatenation in toString.
     */
    @Benchmark
    public void infoBeanToString(Blackhole bh) {
        String str = existingInfo.toString();
        bh.consume(str);
    }

    /**
     * Benchmark: ImageBean toString.
     * Tests simple toString.
     */
    @Benchmark
    public void imageBeanToString(Blackhole bh) {
        String str = existingImage.toString();
        bh.consume(str);
    }

    /**
     * Benchmark: ImageBean getImgIfString - matching.
     * Tests String.contains for matching case.
     */
    @Benchmark
    public void imageBeanGetImgIfStringMatch(Blackhole bh) {
        String result = existingImage.getImgIfString("square");
        bh.consume(result);
    }

    /**
     * Benchmark: ImageBean getImgIfString - not matching.
     * Tests String.contains for non-matching case.
     */
    @Benchmark
    public void imageBeanGetImgIfStringNoMatch(Blackhole bh) {
        String result = existingImage.getImgIfString("banner");
        bh.consume(result);
    }

    // ==================== COLLECTION OPERATIONS ====================

    /**
     * Benchmark: Iterate product images.
     * Simulates image display loop.
     */
    @Benchmark
    public void iterateProductImages(Blackhole bh) {
        for (ImageBean img : existingProduct.getImages()) {
            bh.consume(img.getImg());
        }
    }

    /**
     * Benchmark: Find specific image type in collection.
     * Simulates Utils.getSquareImage pattern.
     */
    @Benchmark
    public void findImageByType(Blackhole bh) {
        String foundImage = null;
        for (ImageBean img : existingProduct.getImages()) {
            if (img.getImgIfString("square") != null) {
                foundImage = img.getImg();
                break;
            }
        }
        bh.consume(foundImage);
    }

    /**
     * Main method to run benchmarks standalone.
     */
    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(ModelBeanBenchmark.class.getSimpleName())
                .forks(1)
                .warmupIterations(2)
                .measurementIterations(3)
                .build();

        new Runner(opt).run();
    }
}
