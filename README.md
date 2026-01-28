# Shapedibles

Shapedibles is a simple dynamic e-commerce web application developed as a case study for analysing software quality, correctness, and deployability.  
The project is based on a classic Java servlet architecture and is currently under development.

---

## Project Overview

The application follows a traditional servlet-based web architecture:

- **Java Servlets** handle HTTP/HTTPS requests and dynamically generate HTML pages.
- **Data persistence** is implemented using a relational SQLite database.
- **Data Access Object (DAO) classes** encapsulate all CRUD (Create, Read, Update, Delete) operations.
- **JavaBeans** are used to transfer data between the persistence layer and the servlets.
- The application is deployed on **Apache Tomcat**.

While the core functionality is present, the system is incomplete and missing some features, such as full navigation between pages and robust implementations of certain components.

---

## Purpose of the Project

Shapedibles was used as a case study for analysing and improving various aspects of software engineering, including:

- Software quality and correctness
- Continuous Integration (CI)
- Formal verification using **JML**
- Automated testing
- Container-based deployment using **Docker**
- Performance benchmarking
- Security assessment

The focus of the project is not the completeness of the application itself, but the evaluation and application of engineering techniques on a realistic system.

---

## Running the Application with Docker

The application can be built and run locally using Docker and Docker Compose.  
No local Java, Maven, or Tomcat installation is required.

### Prerequisites
- Docker
- Docker Compose

---

### Build and Run

From the root of the repository, run:

```bash
docker compose up -d
````

This command will:

1. Build the application from source using a multi-stage Docker build
2. Deploy the generated WAR file to a Tomcat container
3. Start the application in detached mode

---

### Accessing the Application

Once the container is running, the application is available at:

* **HTTPS:** [https://localhost:8443/mia-applicazione/](https://localhost:8443/mia-applicazione/)

> Note: A self-signed TLS certificate is used for HTTPS. Check out the Dockerfile for context.

---

### Stopping the Application

To stop and remove the running containers:

```bash
docker compose down
```

---

## Notes

* The Docker setup is intended for **development and evaluation purposes**.
* The application is still under development and may contain incomplete or experimental features.
```
