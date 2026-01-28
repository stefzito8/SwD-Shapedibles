# -- build --

FROM maven:3.9-eclipse-temurin-21 AS build
WORKDIR /app

COPY pom.xml .
RUN mvn dependency:go-offline

# copy source and build
COPY src ./src
RUN mvn clean package -DskipTests

# -- runtime --

FROM tomcat:9.0-jdk21-openjdk-slim-bullseye

# copy the configured server.xml into the Tomcat config folder.
COPY docker/server.xml /usr/local/tomcat/conf/server.xml

# generating a new .keystore file to prevent a security leak.
RUN keytool -genkeypair \
    -alias tomcat \
    -keyalg RSA \
    -keysize 2048 \
    -storetype PKCS12 \
    -keystore /root/.keystore \
    -validity 3650 \
    -storepass changeit \
    -dname "CN=localhost, OU=Student, O=Demo, L=Salerno, S=Italy, C=IT"

# copy the app.
# if not renamed, the URL is https://localhost:8443/mia-applicazione/
COPY --from=build /app/target/mia-applicazione.war \
     /usr/local/tomcat/webapps/mia-applicazione.war

# open the ports for the outside world.
EXPOSE 8080 8443
