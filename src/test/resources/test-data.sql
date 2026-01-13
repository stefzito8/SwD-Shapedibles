-- Test data for H2 integration tests
-- Provides sample data for testing DAO and Controller-Model integration
-- Matches the exact table and column names expected by DAO implementations

-- Sample products (table: product, columns: CODE, NAME, CURRENT_INFOS)
INSERT INTO product (CODE, NAME, CURRENT_INFOS) VALUES (1, 'Protein Shake Vanilla', 1);
INSERT INTO product (CODE, NAME, CURRENT_INFOS) VALUES (2, 'Protein Shake Chocolate', 2);
INSERT INTO product (CODE, NAME, CURRENT_INFOS) VALUES (3, 'Energy Bar', 3);
INSERT INTO product (CODE, NAME, CURRENT_INFOS) VALUES (4, 'Pre-Workout Mix', 4);
INSERT INTO product (CODE, NAME, CURRENT_INFOS) VALUES (5, 'BCAA Capsules', 5);

-- Sample product info (table: product_info, columns: CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE)
INSERT INTO product_info (CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE) 
VALUES (1, 'Protein Shake Vanilla', 29.99, 'Delicious vanilla flavored protein shake with 25g protein per serving', 100, 'Protein');
INSERT INTO product_info (CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE) 
VALUES (2, 'Protein Shake Chocolate', 29.99, 'Rich chocolate protein shake with 25g protein per serving', 50, 'Protein');
INSERT INTO product_info (CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE) 
VALUES (3, 'Energy Bar', 3.99, 'High protein energy bar for on-the-go nutrition', 200, 'Snack');
INSERT INTO product_info (CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE) 
VALUES (4, 'Pre-Workout Mix', 39.99, 'Pre-workout formula for enhanced performance', 75, 'Supplement');
INSERT INTO product_info (CODE, NAME, PRICE, DESCRIPTION, AVAILABILITY, TYPE) 
VALUES (5, 'BCAA Capsules', 24.99, 'BCAA capsules for muscle recovery', 150, 'Supplement');

-- Sample nutrition data (table: nutritionalValues, columns: PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT)
INSERT INTO nutritionalValues (PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT) 
VALUES (1, 120, 2.0, 0.5, 5.0, 2.0, 1.0, 25.0, 0.3);
INSERT INTO nutritionalValues (PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT) 
VALUES (2, 130, 2.5, 0.8, 6.0, 3.0, 1.5, 25.0, 0.35);
INSERT INTO nutritionalValues (PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT) 
VALUES (3, 200, 8.0, 3.0, 25.0, 10.0, 3.0, 15.0, 0.2);
INSERT INTO nutritionalValues (PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT) 
VALUES (4, 15, 0.0, 0.0, 3.0, 1.0, 0.0, 0.0, 0.5);
INSERT INTO nutritionalValues (PRODUCT_CODE, ENERGY, FATS, SATURATED_FATS, CARBS, SUGARS, FIBERS, PROTEINS, SALT) 
VALUES (5, 5, 0.0, 0.0, 0.0, 0.0, 0.0, 2.5, 0.0);

-- Sample users (table: users, columns: USERNAME, EMAIL, PASS, NAME_SURNAME, GENDER, COUNTRY, BIRTHDAY, USER_ADMIN)
-- password is hashed 'password123'
INSERT INTO users (USERNAME, EMAIL, PASS, NAME_SURNAME, GENDER, COUNTRY, BIRTHDAY, USER_ADMIN) 
VALUES ('testuser', 'testuser@example.com', '5e884898da28047d91684a56a44e8acb', 'Test User', 'M', 'Italy', '1990-01-15', 0);
INSERT INTO users (USERNAME, EMAIL, PASS, NAME_SURNAME, GENDER, COUNTRY, BIRTHDAY, USER_ADMIN) 
VALUES ('adminuser', 'admin@example.com', '5e884898da28047d91684a56a44e8acb', 'Admin User', 'M', 'Italy', '1985-06-20', 1);
INSERT INTO users (USERNAME, EMAIL, PASS, NAME_SURNAME, GENDER, COUNTRY, BIRTHDAY, USER_ADMIN) 
VALUES ('customer', 'customer@example.com', '5e884898da28047d91684a56a44e8acb', 'Regular Customer', 'F', 'USA', '1995-03-10', 0);

-- Sample addresses (table: adresses, columns: ID, user, country, street, city, number, Postal_Code)
INSERT INTO adresses (ID, "user", country, street, city, number, Postal_Code) 
VALUES ('addr1', 'testuser', 'Italy', 'Via Roma', 'Milano', 123, '20100');
INSERT INTO adresses (ID, "user", country, street, city, number, Postal_Code) 
VALUES ('addr2', 'testuser', 'Italy', 'Via Verdi', 'Roma', 456, '00100');
INSERT INTO adresses (ID, "user", country, street, city, number, Postal_Code) 
VALUES ('addr3', 'adminuser', 'Italy', 'Piazza Duomo', 'Firenze', 1, '50100');

-- Sample orders (table: orders, columns: User, code, address, state, order_date, total_cost)
INSERT INTO orders (code, "User", address, state, order_date, total_cost) 
VALUES (1, 'testuser', 'Via Roma 123, Milano 20100, Italy', 'COMPLETED', '2024-01-15', 59.98);
INSERT INTO orders (code, "User", address, state, order_date, total_cost) 
VALUES (2, 'testuser', 'Via Roma 123, Milano 20100, Italy', 'PENDING', '2024-01-20', 29.99);
INSERT INTO orders (code, "User", address, state, order_date, total_cost) 
VALUES (3, 'customer', '123 Main St, New York 10001, USA', 'SHIPPED', '2024-01-22', 43.98);

-- Sample order items (table: Contains, columns: order_code, info_code, Quantity)
INSERT INTO Contains (order_code, info_code, Quantity) VALUES (1, 1, 2);
INSERT INTO Contains (order_code, info_code, Quantity) VALUES (2, 2, 1);
INSERT INTO Contains (order_code, info_code, Quantity) VALUES (3, 3, 5);
INSERT INTO Contains (order_code, info_code, Quantity) VALUES (3, 5, 1);

-- Sample images (table: images, columns: Images_Num, Product_Code, img)
INSERT INTO images (Images_Num, Product_Code, img) VALUES (1, 1, 'protein_vanilla_square.jpg');
INSERT INTO images (Images_Num, Product_Code, img) VALUES (2, 1, 'protein_vanilla_wide.jpg');
INSERT INTO images (Images_Num, Product_Code, img) VALUES (3, 2, 'protein_chocolate_square.jpg');
INSERT INTO images (Images_Num, Product_Code, img) VALUES (4, 3, 'energy_bar_square.jpg');
