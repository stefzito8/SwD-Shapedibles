  
![][image1]

# **Analysis and Improvement of a Dynamic Web Project's Dependability**

**Student Report**

**Presented by:**  
Stefano Nicolò Zito  
Dominykas Kruminis  
Alisher Khaireden

**Università di Salerno, Dipartimento di Informatica**  
**January, 2026**

# **Abstract** {#abstract}

This report presents an analysis and enhancement of *Shapedibles*, a servlet-based e-commerce web application developed as a case study in software engineering practices. The application follows a classic multi-tier architecture, using Java servlets for request handling, Data Access Object (DAO) classes for database interaction and JavaBeans for data transfer, with persistence provided by a relational SQLite database.  
The project focuses on improving confidence in the correctness, reliability and deployability of the application through a combination of formal specification, automated testing and containerisation. Core components of the system, particularly the DAO layer and selected business logic, are formally specified using the Java Modeling Language (JML) and verified with OpenJML. The effectiveness of the test suite is evaluated through code coverage analysis, mutation testing and performance benchmarking of critical components.  
In addition, the application is containerised using Docker and deployed as a reusable image, enabling consistent execution across different environments. The deployment process is documented and designed to support orchestration through Docker Compose. Finally, the project integrates security analysis tools into the continuous integration pipeline to identify vulnerabilities and assess the overall security posture of the application.  
The results demonstrate that the application can be reliably built, tested, deployed and analysed using modern software engineering techniques, providing a structured foundation for future development and improvement.

**Table of Content**

[**Abstract	2**](#abstract)

[**Introduction	5**](#introduction)

[**1\. The application is buildable in CI/CD and locally.	5**](#1-the-application-is-buildable-in-ci/cd-and-locally.)

[**2\. The core methods of the application have a formal specification in JML, verified using OpenJML.	6**](#2-the-core-methods-of-the-application-have-a-formal-specification-in-jml,-verified-using-openjml.)

[2.1. Choosing core methods	6](#2.1-choosing-core-methods)

[2.2. Implementing and checking JML	6](#2.2-implementing-and-checking-jml)

[2.3. Results	7](#2.3-results)

[**3\. Dockerised deployment of the web application	7**](#3-dockerised-deployment-of-the-web-application)

[3.1. Understanding the stack	7](#3.1-understanding-the-stack)

[3.2. The iterative dockerisation process	8](#3.2-the-iterative-dockerisation-process)

[3.2.1. Build, test, fail, learn, repeat	8](#3.2.1-build,-test,-fail,-learn,-repeat)

[3.2.2. The privacy breach and the pivot	8](#3.2.2-the-privacy-breach-and-the-pivot)

[3.2.3 Final Deployment and Pushing to Docker Hub	9](#3.2.3-final-deployment-and-pushing-to-docker-hub)

[3.3. Making it composable	9](#3.3-making-it-composable)

[3.4 Documentation	10](#3.4-documentation)

[3.4.1 Dockerfile Internal Documentation	10](#3.4.1-dockerfile-internal-documentation)

[3.4.2 The README Strategy	10](#3.4.2-the-readme-strategy)

[3.5 Issues, acknowledged yet undealt with	10](#3.5-issues,-acknowledged-yet-undealt-with)

[3.5.1 Keystore password handling	11](#3.5.1-keystore-password-handling)

[3.5.2 Self-signed TLS certificates	11](#3.5.2-self-signed-tls-certificates)

[3.5.3 Lack of container health checks	11](#3.5.3-lack-of-container-health-checks)

[3.5.4 Image size and optimisation	11](#3.5.4-image-size-and-optimisation)

[**4\. The web application has a significant number of test cases	12**](#4-the-web-application-has-a-significant-number-of-test-cases)

[4.1. Methodological selection: Black-Box vs. White-Box testing	12](#4.1-methodological-selection:-black-box-vs.-white-box-testing)

[4.2. Integration strategy: The Modified Sandwich approach	13](#4.2-integration-strategy:-the-modified-sandwich-approach)

[4.3. System testing limitations	13](#4.3-system-testing-limitations)

[**5\. Code coverage is analysed using JaCoCo	13**](#5-code-coverage-is-analysed-using-jacoco)

[5.1. Selection of metrics: TER1 and TER2	13](#5.1-selection-of-metrics:-ter1-and-ter2)

[5.2. Analysis of results and limitations	14](#5.2-analysis-of-results-and-limitations)

[**6\. A mutation testing campaign is conducted to analyse the test cases using PiTest	14**](#6-a-mutation-testing-campaign-is-conducted-to-analyse-the-test-cases-using-pitest)

[6.1. Execution and findings	15](#6.1-execution-and-findings)

[**7\. JMH micro-benchmarks test the performance of the most demanding components of the web application	15**](#7-jmh-micro-benchmarks-test-the-performance-of-the-most-demanding-components-of-the-web-application)

[7.1. Component selection and justification	15](#7.1-component-selection-and-justification)

[7.2. Methodology: Throughput vs. Response Time	16](#7.2-methodology:-throughput-vs.-response-time)

[7.3. Isolation strategy and tool limitations	16](#7.3-isolation-strategy-and-tool-limitations)

[**8 Security mechanisms are implemented in CI/CD	16**](#8-security-mechanisms-are-implemented-in-ci/cd)

[**9 Security is analysed using GitGuardian, Snyk and Sonacube Cloud	17**](#9-security-is-analysed-using-gitguardian,-snyk-and-sonacube-cloud)

[**10 The web application shows no vulnerabilities	17**](#10-the-web-application-shows-no-vulnerabilities)

[**10.1 Solving code Secrets	17**](#10.1-solving-code-secrets)

[**10.2 Solving Vulnerabilities	18**](#10.2-solving-vulnerabilities)

[**11 Role of Large Language Model in the study	18**](#11-role-of-large-language-model-in-the-study)

[11.1 Conceptual understanding	19](#11.1-conceptual-understanding)

[11.2 Artefact generation	19](#11.2-artefact-generation)

[**Conclusion	20**](#conclusion)

[**References	21**](#references)

# **Introduction** {#introduction}

The project analysed in this report is *Shapedibles*, a simple dynamic e-commerce web application designed to support online transactions.The application served as our case study for analysing software quality, correctness and deployability through a range of engineering techniques.  
The system was made using a classic servlet-based architecture. In this model, Java objects named servlets  are responsible for handling HTTP requests (HTTPS in the deployed configuration) and dynamically generating HTML responses, building pages.  
The application data used is stored in a relational database (SQLite) and accessed through a set of Data Access Object (DAO) classes. These classes encapsulate all CRUD (Create, Read, Update, Delete) operations and transfer data using JavaBean objects, which the servlets can then use and consume.  
While functional, the project is currently under development and is missing key features, such as link between pages and having a precarious implementation of other ones.  
This report documents the process of analysing and enhancing the application through continuous integration, formal verification using JML, automated testing, container-based deployment, performance benchmarking and security assessment.

# **1 The application is buildable in CI/CD and locally.** {#1-the-application-is-buildable-in-ci/cd-and-locally.}

[https://github.com/stefzito8/SwD-Shapedibles](https://github.com/stefzito8/SwD-Shapedibles)

# **2 The core methods of the application have a formal specification in JML, verified using OpenJML.** {#2-the-core-methods-of-the-application-have-a-formal-specification-in-jml,-verified-using-openjml.}

## **2.1 Choosing core methods** {#2.1-choosing-core-methods}

The core methods chosen for this task are those related to the DAO classes. As these methods reside at the very bottom of our architecture, verifying them allows us to prevent contract errors that, if unchecked, could propagate through the rest of the application. In addition to the DAOs, basic JML specifications have been added to the Bean classes' methods, since these are used by the DAO classes and are also checked by OpenJML when invoked. The Cart class also has methods specified using JML, as it manages a unique object bound to the user session that manipulates bean objects.

## **2.2 Implementing and checking JML** {#2.2-implementing-and-checking-jml}

The DAO classes are divided into two directories within the project:

* Dao: This directory stores the interfaces that define the methods.  
* DaoDataSources: This directory contains the actual DAO classes which implement the aforementioned interfaces.

The files in both directories have been annotated with JML. Since the system supports inheritance in specifications, a specification declared in an interface method is automatically applied to all its implementations. Therefore, pre-conditions and post-conditions are applied to the method declarations in the interfaces, while assert statements, loop specifications and variable specifications (such as nullable) are applied within the DaoDataSource classes.

As previously mentioned, the Bean classes received the minimum specifications required to enable the DAO classes to invoke their methods: getter methods were marked as pure and setter methods were marked with assignable statements. The Cart class received specifications for the addProduct and deleteProduct methods, ensuring that the operations for adding and deleting units from the cart are correctly implemented.

After being added to the classes, the specifications were statically analyzed with OpenJML first locally and then in CI/CD by integrating OpenJML check operations into the Maven Package GitHub Action.

##  **2.3 Results** {#2.3-results}

The results of these tasks are successful, as demonstrated by the completion of the Maven Package action in GitHub. The static analysis revealed no contradictions between the specifications of the chosen methods and their implementations.

# **3 Dockerised deployment of the web application** {#3-dockerised-deployment-of-the-web-application}

A Docker image of the web application has been created and pushed on Docker Hub. The image is designed to be easily accessible, readily orchestrated and executed in a containerised environment, ensuring portability and reproducibility across different operating systems and host configurations.

Before I go on, note that you can find the Dockerfile and docker-compose.yml files on the GitHub page of the project and that you may review the image [here](https://hub.docker.com/repository/docker/justalish/mia-applicazione/general), please.

## **3.1 Understanding the stack** {#3.1-understanding-the-stack}

‘*Minimising headaches.*’

Before containerising the application, the underlying technology stack was analysed. As a developer primarily experienced with *TypeScript* and *Preact*, transitioning to a more configuration-heavy Java/XML ecosystem configuration was a significant shift.

The use of *Fedora 43 KDE Plasma* was a turning point; its reliable environment and streamlined package management made installing the JDK and managing Java environment variables much more approachable for a first-timer. To ensure full control over the deployment and to avoid the configuration choices made by other team members, a custom `server.xml` was authored from scratch. This ensured the Tomcat instance was tuned specifically for this container’s requirements rather than relying on external defaults.

The application is strictly configured to serve HTTPS traffic. Special attention was given to understanding TLS certificates and Java .keystore files, which are necessary for Tomcat to handle secure handshakes.

## **3.2 The iterative dockerisation process** {#3.2-the-iterative-dockerisation-process}

‘*Commands used.*’

The application was containerised by defining a Dockerfile that builds upon an official Apache Tomcat base image. The Dockerfile installs the required runtime dependencies, configures the server, and deploys the application WAR file into the appropriate Tomcat directory.

### **3.2.1 Build, test, fail, learn, repeat** {#3.2.1-build,-test,-fail,-learn,-repeat}

The containerisation process was an iterative cycle of trial, error and refinement:

- Initial attempt: created a basic Dockerfile using default Tomcat configurations, which resulted in a failure.  
  - Reason: standard Tomcat defaults were insufficient for our specific `.war` requirements.  
- Custom configuration: authored a server.xml via simply uncommenting the SSL/TLS HTTP/1.1 Connector on port 8443 block of the file and specifying a specific certificate position, password, keystore type, encryption type and alias, which also resulted in a failure.  
  - Reason: while a step in the right direction, the application also required secure HTTPS communication, which the container lacked.  
- Manual security: Added a pre-generated .keystore file from the local Fedora environment, which finally resulted in an initial success.  
  - Nuance: while the app worked, it created a massive privacy breach vulnerability.

### **3.2.2 The privacy breach and the pivot** {#3.2.2-the-privacy-breach-and-the-pivot}

During the testing phase, it became clear that including a local .keystore file in the build context was a critical security risk. If pushed to a public repository like Docker Hub, the private credentials would be compromised. To resolve this, the Dockerfile was completely rewritten to automate security. Instead of copying a sensitive file, the keytool command was integrated directly into the `RUN` layer:  
```` ```Dockerfile ````  
`# generating a new .keystore file to prevent a security leak`  
`RUN keytool -genkeypair -alias tomcat -keyalg RSA -keysize 2048 \`  
    `-storetype PKCS12 -keystore /root/.keystore -validity 3650 \`  
    `-storepass changeit -dname "CN=localhost, OU=Student, O=Demo, L=Salerno, S=Italy, C=IT"`  
```` ``` ````  
This shift ensured that each build generated its own fresh credentials, keeping the developer's local environment separate from the public image.

### **3.2.3 Final deployment and pushing to Docker Hub** {#3.2.3-final-deployment-and-pushing-to-docker-hub}

Once the "build-test-fail" loops were resolved and the Java XML configurations were understood and stabilised, the final image was built using `docker build -t mia-applicazione:vN.N .`, then – after logging into docker via `docker login` – the generated image, tagged as justalish/mia-applicazione:v1.3, was pushed to Docker Hub. This final version encapsulates the custom server.xml, the automated keystore generation, and the .war application, providing a "plug-and-play" deployment experience that abstracts the underlying implementation details from the end user.

## **3.3 Making it composable** {#3.3-making-it-composable}

‘C*ommands not used, on purpose.*’

To simplify execution and orchestration, a docker-compose.yml file was provided to minimise the need for long, verbose Docker commands. Docker Compose is used to define how the container should be run, including port mappings and restart policies, without embedding runtime configuration into the image itself.  
```` ```yml ````  
`services:`  
  `web-app:`  
    `image: justalish/mia-applicazione:v1.3`  
    `ports:`  
      `- "8443:8443"`  
      `- "8080:8080"`  
    `restart: unless-stopped`  
```` ``` ````  
Notably, the Compose configuration is intentionally limited to runtime concerns and does not include build instructions. This design choice ensures a clear separation between image creation and container execution, allowing the same image to be reused consistently across different environments.

## **3.4 Documentation** {#3.4-documentation}

‘*Making sure we’re equal.*’

We think that a good piece of open-source software is effectively useless if no one can understand it, which is especially apparent in complex Java-based deployment. Recognising that, effort was put into documentation.

### **3.4.1 Dockerfile internal documentation** {#3.4.1-dockerfile-internal-documentation}

Every layer of the Dockerfile was commented to explain the why behind the keytool parameters and the file paths, making it accessible for future maintainers.

### **3.4.2 The README strategy** {#3.4.2-the-readme-strategy}

A comprehensive README was written to bridge the gap between source code and production. It serves three roles:

1. Repo Guide: Explaining the GitHub project structure.  
2. Brief Tomcat Manual: Detailing how .war containers operate within Apache 9.0.  
3. Deployment Guide: Providing a "one-command" startup guide using Docker Compose.

## **3.5 Issues, acknowledged yet undealt with** {#3.5-issues,-acknowledged-yet-undealt-with}

‘*Compromises necessary.*’

While the final Dockerised deployment achieves its primary goal of providing a secure, reproducible, and portable execution environment, several known limitations remain. These issues were consciously identified during development but left unresolved due to scope, time constraints, or because they fell outside the immediate requirements of the project.

### **3.5.1 Keystore password handling** {#3.5.1-keystore-password-handling}

Although the keystore is generated dynamically at build time to avoid credential leakage, the keystore password is currently hard-coded within the Dockerfile. In a production-grade deployment, this would be considered suboptimal. A more robust approach would involve injecting sensitive values via environment variables or Docker secrets at runtime, allowing credentials to be rotated without rebuilding the image. For the purposes of this project, the chosen approach prioritises clarity and reproducibility over operational flexibility.

### **3.5.2 Self-signed TLS certificates** {#3.5.2-self-signed-tls-certificates}

The deployment currently relies on a self-generated TLS certificate, which is sufficient for enabling encrypted transport but does not provide trusted identity verification and results in browser warnings. During development, it was recognised that a more appropriate solution would involve the use of TLS certificates issued or approved by the University of Salerno, aligning the deployment with institutional security policies and trusted certificate chains.

Obtaining and integrating such certificates would require coordination with the university’s IT or security services, including validation of domain ownership and compliance with internal infrastructure requirements. As this process extends beyond the technical scope of the project and depends on external administrative procedures, it was acknowledged but not pursued during implementation. Should the application be deployed within an official university-managed environment, replacing the self-generated certificate with institutionally issued credentials would be a necessary step.

### **3.5.3 Lack of container health checks** {#3.5.3-lack-of-container-health-checks}

The Docker image does not define an explicit HEALTHCHECK. Container health was instead assessed through Tomcat startup logs and manual testing. While adequate during development, the absence of a health check limits automated orchestration capabilities and would reduce observability in more complex deployment scenarios.

### **3.5.4 Image size and optimisation** {#3.5.4-image-size-and-optimisation}

The deployment relies on the official Apache Tomcat base image, prioritising stability and documentation over minimal footprint. No image size optimisation techniques (such as multi-stage builds or distroless base images) were applied. This decision was intentional, favouring transparency and maintainability over aggressive optimisation.

# **4 The web application has a significant number of test cases** {#4-the-web-application-has-a-significant-number-of-test-cases}

The SwD-Shapedibles application is supported by a substantial test suite comprising around 1000 test cases. This volume is not arbitrary but rather the result of applying distinct testing methodologies tailored to the specific responsibilities of each architectural layer. To effectively manage this scale and support efficient regression strategies, the project implements custom JUnit 5 tagging through categories.UnitTest and categories.IntegrationTest. This notable organizational feature enables selective test execution, allowing the team to differentiate between rapid, frequent unit tests and slower, periodic integration sweeps.

## **4.1 Methodological selection: Black-Box vs. White-Box testing** {#4.1-methodological-selection:-black-box-vs.-white-box-testing}

To balance thoroughness with efficiency, a hybrid testing strategy was adopted.  
For the Model Layer, specifically the Beans and Data Access Objects (DAOs), the team employed a Black-Box testing approach. These components act primarily as data carriers and validation enforcement points. Consequently, the internal structure of a ProductBean or UserBean is less critical than its adherence to external specifications. By treating these classes as opaque entities, we utilized Equivalence Partitioning and Boundary Value Analysis to rigorously test input handling. This ensured that the domain constraints, such as preventing negative prices or enforcing string limits defined in the JSP forms, were validated strictly against requirements, regardless of the underlying implementation.  
In contrast, the Control Layer required a White-Box strategy. The controllers in this architecture manage complex decision trees, including authentication flows, session handling, and conditional routing. A black-box approach would likely miss subtle execution paths, such as specific error-handling blocks or edge cases in AJAX detection logic. Therefore, we designed tests based on the internal logic of the code, explicitly targeting Statement Coverage and Branch Coverage. This ensured that every logical branch, including exception handling for database failures, was exercised, verifying the robustness of the application's "nervous system".

## **4.2 Integration strategy: The Modified Sandwich approach** {#4.2-integration-strategy:-the-modified-sandwich-approach}

For Integration Testing, we selected a "Modified Sandwich" strategy. This approach was favored over a "Big Bang" integration because unit tests for the bottom layer (Model) were already robust. The strategy involved integrating the middle layer (Controllers) with the lower layer (Model/Database) while effectively simulating the upper layer (View/Filters). This allowed us to validate the critical path of data flow \- from the H2 test database through the controller logic \- without the overhead and complexity of a full UI deployment.

## **4.3 System testing limitations** {#4.3-system-testing-limitations}

It is important to acknowledge the limitations regarding System Testing. While end-to-end functional testing was considered, it was deemed infeasible for this phase due to the lack of an embedded servlet container in the test infrastructure. Without a running container to compile and render JSP pages, we focused our efforts on verifying the logic immediately preceding the view layer, ensuring that the correct attributes and forwarding paths were set, even if the final HTML rendering was not explicitly tested.

# **5 Code coverage is analysed using JaCoCo** {#5-code-coverage-is-analysed-using-jacoco}

To provide a quantitative measure of the test suite's thoroughness, we employed JaCoCo. This tool is great for its ability to generate granular metrics regarding bytecode execution, which served as a primary indicator of our White-Box testing effectiveness.

## **5.1 Selection of metrics: TER1 and TER2** {#5.1-selection-of-metrics:-ter1-and-ter2}

The analysis prioritized two specific metrics derived from IEEE standards:

1. TER1 (Instruction Coverage): This measures the percentage of executable code instructions run during testing.  
2. TER2 (Branch Coverage): This measures the percentage of control flow branches executed.

Tracking TER2 was particularly critical for this project. In web applications handling sensitive logic like user authentication or cart management, high instruction coverage can be deceptive. It is entirely possible to execute a method's lines without triggering every decision outcome (e.g., executing an if block but never the else). By enforcing a target of roughly 70% for Branch Coverage, we ensured that the decision logic itself, not just the linear execution, was solid. It’s worth mentioning that we’ve also set a target of around 80% for Instruction Coverage.

## **5.2 Analysis of results and limitations** {#5.2-analysis-of-results-and-limitations}

The project successfully achieved instruction coverage of 95% and branch coverage of 80%, surpassing the initial quality targets. However, the analysis revealed areas where coverage metrics must be interpreted with context. For instance, the config package exhibited 0% coverage. This was a deliberate exclusion rather than an oversight. Because this package handles the application's startup context and listener initialization, testing it would require a fully running servlet container. Mocking the entire servlet context to achieve artificial coverage here would have resulted in brittle tests that offered little value regarding production behavior. This underscores that while coverage is a necessary metric for identifying untested logic, it is not a standalone guarantee of quality.

# **6 A mutation testing campaign is conducted to analyse the test cases using PiTest** {#6-a-mutation-testing-campaign-is-conducted-to-analyse-the-test-cases-using-pitest}

We wanted to ensure that the tests were sensitive to even minimal changes in business logic, such as a subtle error in a price calculation or a bypassed authorization check.

## **6.1 Execution and findings** {#6.1-execution-and-findings}

The campaign yielded a strong Mutation Coverage score of 83% and a Test Strength of 89%. The analysis of the "surviving mutants" provided valuable insights into the suite's limitations. A notable portion of these survivors were identified as "equivalent mutants" \- changes that do not alter the program's observable behavior, such as removing a logging statement or modifying a toString() method. Since these changes do not impact functional logic, the tests correctly continued to pass.  
However, the campaign also uncovered valid gaps, particularly within the Controller layer's exception-handling logic. Certain mutations within try-catch blocks survived, indicating that while the tests triggered the exception paths (satisfying JaCoCo coverage), they did not always rigorously assert the system's state after the exception was caught. This finding validates the use of mutation testing, as it exposed weaknesses in error-handling verification that standard coverage metrics had missed.

# **7 JMH micro-benchmarks test the performance of the most demanding components of the web application** {#7-jmh-micro-benchmarks-test-the-performance-of-the-most-demanding-components-of-the-web-application}

Functional correctness is insufficient if the system cannot scale. To address non-functional requirements, we employed the Java Microbenchmark Harness to evaluate the performance of the application's most critical components.

## **7.1 Component selection and justification** {#7.1-component-selection-and-justification}

Rather than attempting to benchmark the entire application, we targeted specific components based on their execution frequency and computational complexity:

1. Authentication Filter: This component intercepts every single HTTP request. Any latency here scales linearly with traffic, making it a potential global bottleneck.  
2. Cart Operations: The shopping cart logic involves iterating over collections of items, presenting a risk of *O(n)* complexity issues as cart sizes increase.  
3. Database Access (DAO): As I/O operations are typically the slowest part of any web application, measuring the overhead of connection acquisition and query execution was essential.

## **7.2 Methodology: Throughput vs. Response Time** {#7.2-methodology:-throughput-vs.-response-time}

We selected different measurement modes depending on the operational context. Throughput was the primary metric for the Authentication Filter and Controller Routing. In a high-traffic e-commerce environment, the server's capacity to handle concurrent requests is the defining metric for scalability.  
Conversely, for Cart Operations and Database Searches, we focused on Average Time (latency). These operations directly impact the user experience \- a user perceives the delay when adding an item to the cart or searching for a product, making latency the more relevant metric for satisfaction.

## **7.3 Isolation strategy and tool limitations** {#7.3-isolation-strategy-and-tool-limitations}

To benchmark the Data Access Object (DAO) layer without the noise of network latency or disk I/O, we utilized an H2 in-memory database as a test double.  
We acknowledge the limitation that H2 does not perfectly replicate the performance characteristics of the production SQLite database. However, this trade-off was acceptable because our goal was to identify algorithmic bottlenecks rather than absolute production latency. By removing I/O variables, the benchmarks successfully highlighted code-level inefficiencies, such as the recalculation of cart totals on every read operation, providing a clear path for optimization that functional testing could not have revealed.

# **8 Security mechanisms are implemented in CI/CD** {#8-security-mechanisms-are-implemented-in-ci/cd}

To implement security measures in CI/CD we have created a custom security rule around the main branch of the project, this rules imposes that commits on the main branch of the project must pass a Snyk and Sonacloud inspections, (realized through actions, as explained in the next section) showing no new vulnerabilities have been created inside the project.  
All of the github actions have also been realized following a minimal permission approach and with the correct management of secrets, making sure to leave no exposed hardcoded variables in them. 

# **9 Security is analysed using GitGuardian, Snyk and Sonacube Cloud** {#9-security-is-analysed-using-gitguardian,-snyk-and-sonacube-cloud}

The code in the repository has been analyzed with all three of the requested services. Snyk and Sonacube Cloud have been integrated in CD/CI with github actions.  
The results of Snyk and Sonacube Cloud analysis are fully visible through their action’s results, and in the next section we will talk about what vulnerabilities have emerged and how they were solved.  
As for the GitGuardian analysis, it only showed two secrets in its original analysis and none in  following analysises. as shown in the image:  
![][image2]  
As for the vulnerabilities, the ways these secrets were solved is relayed in the next section of this document.

# **10 The web application shows no vulnerabilities** {#10-the-web-application-shows-no-vulnerabilities}

# **10.1 Solving code Secrets** {#10.1-solving-code-secrets}

Both the code secrets revealed by GitGuardian, where relative to exposed generic Passwords.  
The First one revealed itself to be a false alarm, GitGuardian was misunderstanding a piece of text in a HTML label posed before a password insertion prompt for  a generic password being inserted. The secret was simply ignored.  
The Second Secret was also not a real risk but helped make the project cleaner. Originally, the project did not use a SQLite database stored inside the project itself, but relied on a connection to a classic SQL database. Although the change from classic SQL to SQLite happened during Task1, to better assist the usage of  CI/CD, a file called DriverManagerConnectionPool.java was still present in the control folder of the project and contained hardcoded credentials to the original database connection. Even if this wasn’t a risk anymore, since the connection to that DB was eliminated, the file was still deleted from the project, resolving the secret. 

# **10.2 Solving Vulnerabilities** {#10.2-solving-vulnerabilities}

In total, 71 vulnerabilities have been found by Snyk, of this 71, 70 revealed themself to be false alarms, they were all “Use of Hardcoded Credential” and were relative to the system signaling the use of hardcoded credentials in the testing code, which is not a real vulnerability since this code is not an actually reachable from an outside attacker.  
The only real vulnerability found by Snyk was a “Trust Boundary Violation”. The filter.java class was saving data provided by the user in a session, considered a secure boundary in the code, without checking if it was valid data or cleaning it from potentially dangerous characters, making the system vulnerable to *CRLF* injection. The issue was solved by simply implementing the correct validation and cleaning mechanism for the user data inside of the filter.java class. 

# **11 Role of Large Language Model in the study** {#11-role-of-large-language-model-in-the-study}

*Large Language Models* (LLMs) were used as a supporting tool throughout the development and analysis of the project. Their role was limited to assistance in understanding unfamiliar technologies and in generating auxiliary artefacts, while all architectural decisions, implementations, and validations were performed and reviewed by the authors. The contribution of LLMs can be divided into two main areas: *conceptual understanding* and *artefact generation*.

## **11.1 Conceptual understanding** {#11.1-conceptual-understanding}

LLMs were primarily used to support the understanding of technologies and frameworks that were not part of the authors’ prior background. In particular, they were employed to clarify the syntax and semantics of Docker Compose .yml files, the behaviour of Docker images and tags, and common Git workflows, including error recovery and retrying failed operations.

Additionally, LLMs were used to assist in navigating and understanding the structure of the Apache Tomcat 9.0 server, including its directory hierarchy and configuration files. This support was especially valuable given that the primary development background of some contributors was in TypeScript rather than Java. In this context, LLMs helped explain established Java enterprise patterns, such as the DAO pattern, the separation between interfaces and implementations, and the interaction between servlets, beans, and persistence layers.

In all cases, LLMs were used as an explanatory aid to accelerate learning and reduce onboarding time, rather than as an authoritative source. The information provided was cross-checked against official documentation and validated through experimentation.

## **11.2 Artefact generation** {#11.2-artefact-generation}

LLMs were also used to assist in the generation of auxiliary artefacts that support development and analysis. These included initial drafts of unit tests, Java Modeling Language (JML) specifications for selected methods, and configuration files related to testing and verification workflows.

In particular, LLM-generated content was used as a starting point for writing JML annotations for core methods and for scaffolding unit test structures. All generated artefacts were manually reviewed, corrected, and refined to ensure consistency with the actual behaviour of the application and to meet the requirements of the analysis tools used, such as OpenJML.

Importantly, LLMs were not used to generate core application logic or architectural components. Their role in artefact generation was limited to reducing repetitive effort and providing structured templates, while correctness, completeness, and suitability remained the responsibility of the authors.

# **Conclusion** {#conclusion}

The work presented in this report confirms that the application of rigorous software engineering practices can significantly elevate the reliability, security and deployability of a legacy servlet-based application like Shapedibles. By integrating formal verification via OpenJML, the project established a proved foundation for the application's core data interactions, ensuring strict adherence to specifications within the DAO and Bean layers without revealing logical contradictions. This mathematical approach to correctness was complemented by a robust containerization strategy; the move to a Docker-based architecture not only resolved environment inconsistencies but also enforced security through automated keystore generation and reproducible deployments via Docker Compose.

Furthermore, the project’s multi-layered testing strategy demonstrated the value of combining distinct methodologies. The hybrid approach of black-box and white-box testing resulted in a suite of approximately 1000 test cases, achieving 95% instruction coverage. Crucially, the inclusion of mutation testing with PiTest went beyond standard metrics to expose subtle weaknesses in the controller layer's exception handling.

Finally, the integration of performance benchmarking and automated security analysis into the CI/CD pipeline ensured the system was not only functional but also efficient and secure. The resolution of critical vulnerabilities, such as Trust Boundary Violations, and the identification of algorithmic bottlenecks via JMH, transformed the application from a precarious case study into a hardened software artifact. Ultimately, this project successfully demonstrates that modern DevOps and verification techniques can be effectively applied to traditional Java architectures to create a reliable and maintainable system.

# **References** {#references}

**GITHUB**. *How to generate unit tests with GitHub Copilot: Tips and examples*. \[online\]. 2024\. \[viewed 28 January 2026\]. Available from: [https://github.blog/ai-and-ml/github-copilot/how-to-generate-unit-tests-with-github-copilot-tips-and-examples/](https://github.blog/ai-and-ml/github-copilot/how-to-generate-unit-tests-with-github-copilot-tips-and-examples/)

**APACHE SOFTWARE FOUNDATION**. *Apache Tomcat 9.0: SSL/TLS Configuration How-To*. \[online\]. 2024\. \[viewed 28 January 2026\]. Available from: [https://tomcat.apache.org/tomcat-9.0-doc/ssl-howto.html](https://tomcat.apache.org/tomcat-9.0-doc/ssl-howto.html)

**ORACLE CORPORATION**. *keytool – Key and Certificate Management Tool*. \[online\]. 2021\. \[viewed 28 January 2026\]. Available from: [https://docs.oracle.com/en/java/javase/17/docs/specs/man/keytool.html](https://docs.oracle.com/en/java/javase/17/docs/specs/man/keytool.html)

**STACK OVERFLOW**. *Does “Unit Testing” fall under white box or black box testing?*. \[online\]. 2012\. \[viewed 28 January 2026\]. Available from: [https://stackoverflow.com/questions/9892963/does-unit-testing-falls-under-white-box-or-black-box-testing](https://stackoverflow.com/questions/9892963/does-unit-testing-falls-under-white-box-or-black-box-testing)

**IEEE**. *610.12-1990 \- IEEE Standard Glossary of Software Engineering Terminology*. \[online\]. 1990\. \[viewed 28 January 2026\]. Available from: [https://ieeexplore.ieee.org/document/159342](https://ieeexplore.ieee.org/document/159342)

**JUNIT**. *JUnit 5 User Guide: Writing Tests – Tagging and Filtering*. \[online\]. 2024\. \[viewed 28 January 2026\]. Available from: [https://junit.org/junit5/docs/current/user-guide/\#writing-tests-tagging-and-filtering](https://junit.org/junit5/docs/current/user-guide/#writing-tests-tagging-and-filtering)

**GEEKSFORGEEKS**. *Docker Compose YAML Explained: A Deep Dive into Configuration*. \[online\]. 2023\. \[viewed 28 January 2026\]. Available from: [https://www.geeksforgeeks.org/devops/docker-compose-yaml-explained-a-deep-dive-into-configuration/](https://www.geeksforgeeks.org/devops/docker-compose-yaml-explained-a-deep-dive-into-configuration/)

**DOCKER**. *Writing a Dockerfile*. \[online\]. 2024\. \[viewed 28 January 2026\]. Available from: [https://docs.docker.com/get-started/docker-concepts/building-images/writing-a-dockerfile/](https://docs.docker.com/get-started/docker-concepts/building-images/writing-a-dockerfile/)

**COURSERA**. *Introduction to Containers w/ Docker, Kubernetes & OpenShift*. \[online\]. 2024\. \[viewed 28 January 2026\]. Available from: [https://www.coursera.org/learn/ibm-containers-docker-kubernetes-openshift](https://www.coursera.org/learn/ibm-containers-docker-kubernetes-openshift)

[image1]: <data:image/png;base64,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>

[image2]: <data:image/png;base64,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>