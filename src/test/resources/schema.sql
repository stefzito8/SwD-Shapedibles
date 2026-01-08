-- Schema for H2 test database
-- Matches the exact table and column names expected by DAO implementations

-- Drop tables if they exist (for clean reset)
DROP TABLE IF EXISTS Contains;
DROP TABLE IF EXISTS orders;
DROP TABLE IF EXISTS adresses;
DROP TABLE IF EXISTS images;
DROP TABLE IF EXISTS nutritionalValues;
DROP TABLE IF EXISTS product_info;
DROP TABLE IF EXISTS product;
DROP TABLE IF EXISTS users;

-- Product table (ProductDaoDataSource.TABLE_NAME = "product")
-- Columns: CODE, NAME, CURRENT_INFOS
CREATE TABLE product (
    CODE INT PRIMARY KEY AUTO_INCREMENT,
    NAME VARCHAR(100) NOT NULL,
    CURRENT_INFOS INT
);

-- Product info table (InfoDaoDataSource.TABLE_NAME = "product_info")
-- Columns: CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE
CREATE TABLE product_info (
    CODE INT PRIMARY KEY AUTO_INCREMENT,
    NAME VARCHAR(100),
    PRICE DECIMAL(10,2) NOT NULL,
    DESCRIPTION VARCHAR(500),
    AVAILABILITY INT NOT NULL DEFAULT 0,
    TYPE VARCHAR(50)
);

-- Nutrition table (NutritionTableDaoDataSource.TABLE_NAME = "nutritionalValues")
-- Columns: PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT
CREATE TABLE nutritionalValues (
    PRODUCT_CODE INT PRIMARY KEY,
    ENERGY INT,
    FATS DECIMAL(10,2),
    SATURATED_FATS DECIMAL(10,2),
    CARBS DECIMAL(10,2),
    SUGARS DECIMAL(10,2),
    FIBERS DECIMAL(10,2),
    PROTEINS DECIMAL(10,2),
    SALT DECIMAL(10,2)
);

-- Images table (ImageDaoDataSource.TABLE_NAME = "images")
-- Columns: Images_Num, Product_Code, img
CREATE TABLE images (
    Images_Num INT AUTO_INCREMENT,
    Product_Code INT NOT NULL,
    img VARCHAR(255),
    PRIMARY KEY (Images_Num, Product_Code)
);

-- Users table (UserDaoDataSource.TABLE_NAME = "users")
-- Columns: USERNAME, EMAIL, PASS, NAME_SURNAME, GENDER, COUNTRY, BIRTHDAY, USER_ADMIN
CREATE TABLE users (
    USERNAME VARCHAR(50) PRIMARY KEY,
    EMAIL VARCHAR(100) NOT NULL,
    PASS VARCHAR(255) NOT NULL,
    NAME_SURNAME VARCHAR(100),
    GENDER VARCHAR(10),
    COUNTRY VARCHAR(50),
    BIRTHDAY VARCHAR(20),
    USER_ADMIN INT DEFAULT 0
);

-- Addresses table (AddressDaoDataSource.TABLE_NAME = "adresses") - Note: typo in original code
-- Columns: ID, user, country, street, city, number, Postal_Code
CREATE TABLE adresses (
    ID VARCHAR(50),
    "user" VARCHAR(50) NOT NULL,
    country VARCHAR(50),
    street VARCHAR(200),
    city VARCHAR(100),
    number INT,
    Postal_Code VARCHAR(20),
    PRIMARY KEY (ID, "user")
);

-- Orders table (OrderDaoDataSource.TABLE_NAME = "orders")
-- Columns: User, code, address, state, order_date, total_cost
-- Note: "user" is a reserved word in H2, must be quoted
CREATE TABLE orders (
    code INT PRIMARY KEY AUTO_INCREMENT,
    "User" VARCHAR(50) NOT NULL,
    address VARCHAR(500),
    state VARCHAR(50) DEFAULT 'PENDING',
    order_date VARCHAR(50),
    total_cost DECIMAL(10,2)
);

-- Contain table (ContainDaoDataSource.TABLE_NAME = "Contains")
-- Columns: order_code, info_code, Quantity
CREATE TABLE Contains (
    order_code INT,
    info_code INT NOT NULL,
    Quantity INT NOT NULL DEFAULT 1,
    PRIMARY KEY (order_code, info_code)
);
