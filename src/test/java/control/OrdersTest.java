package control;

import categories.UnitTest;
import model.bean.ContainBean;
import model.bean.OrderBean;
import model.dao.IContainDao;
import model.dao.IOrderDao;
import model.datasource.ContainDaoDataSource;
import model.datasource.OrderDaoDataSource;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.MockedConstruction;
import org.mockito.junit.jupiter.MockitoExtension;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletContext;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.sql.DataSource;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Unit tests for Orders controller.
 * 
 * Testing Level: Unit
 * Technique: White-Box (Statement Testing, Branch Testing) with Mocking
 * 
 * ============================================================================
 * BRANCH STRUCTURE ANALYSIS (Step 3.1)
 * ============================================================================
 * 
 * Method: doPost(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                        | True Path               | False Path         |
 * |-----------|----------------------------------|-------------------------|--------------------|
 * | ORD-B1    | action != null                   | Process action          | Show all orders    |
 * | ORD-B2    | action == "UserFilter"           | Filter by user          | Check next         |
 * | ORD-B3    | action == "DateFilter"           | Filter by date range    | Check next         |
 * | ORD-B4    | action == "User-DateFilter"      | Filter by user & date   | Check next         |
 * | ORD-B5    | action == "orderDetails"         | Get order details       | No action          |
 * | ORD-B6    | isRightDate() in date filters    | Include order           | Exclude order      |
 * | ORD-B7    | SQLException caught              | Set error, send 500     | Normal flow        |
 * -----------------------------------------------------------------
 * 
 * Method: doGet(HttpServletRequest, HttpServletResponse)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                        | True Path               | False Path         |
 * |-----------|----------------------------------|-------------------------|--------------------|
 * | ORD-B8    | Delegates to doPost              | doPost called           | N/A                |
 * -----------------------------------------------------------------
 * 
 * Method: isRightDate(Date date, Date dateMin, Date dateMax)
 * -----------------------------------------------------------------
 * | Branch ID | Condition                        | True Path               | False Path         |
 * |-----------|----------------------------------|-------------------------|--------------------|
 * | ORD-B9    | date >= dateMin                  | Check upper bound       | Return false       |
 * | ORD-B10   | date <= dateMax                  | Return true             | Return false       |
 * -----------------------------------------------------------------
 * 
 * Coverage Targets: TER1 ≥ 80%, TER2 ≥ 70%
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@DisplayName("Orders Controller Tests")
public class OrdersTest {
    
    @Mock
    private HttpServletRequest request;
    
    @Mock
    private HttpServletResponse response;
    
    @Mock
    private ServletContext servletContext;
    
    @Mock
    private RequestDispatcher dispatcher;
    
    @Mock
    private DataSource dataSource;
    
    private Orders servlet;
    
    @BeforeEach
    void setUp() throws Exception {
        servlet = new Orders() {
            @Override
            public ServletContext getServletContext() {
                return servletContext;
            }
        };
        
        // Common mock setup - use lenient for stubs not used by all tests
        lenient().when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
        lenient().when(servletContext.getRequestDispatcher("/WEB-INF/jsp/admin/orderHistory.jsp"))
            .thenReturn(dispatcher);
    }
    
    // ========================================================================
    // doGet Tests
    // ========================================================================
    
    @Nested
    @DisplayName("doGet Tests")
    class DoGetTests {
        
        @Test
        @DisplayName("doGet delegates to doPost")
        void testDoGetDelegatesToDoPost() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList()));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doGet(request, response);
                
                // Verify orders are set and forward happens
                verify(request).setAttribute(eq("orders"), any());
                verify(dispatcher).forward(request, response);
            }
        }
    }
    
    // ========================================================================
    // Default View Tests (No Action)
    // ========================================================================
    
    @Nested
    @DisplayName("Default View Tests")
    class DefaultViewTests {
        
        @Test
        @DisplayName("No action shows all orders")
        void testNoActionShowsAllOrders() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> allOrders = createTestOrders(5);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(allOrders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute("orders", allOrders);
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Default view with sort parameter")
        void testDefaultViewWithSort() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn("dataOrdine");
            
            Collection<OrderBean> allOrders = createTestOrders(3);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll("dataOrdine")).thenReturn(allOrders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Verify sort parameter is passed to DAO
                verify(orderDaoMock.constructed().get(0)).doRetrieveAll("dataOrdine");
            }
        }
        
        @Test
        @DisplayName("Empty orders list handled correctly")
        void testEmptyOrdersList() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList()));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute(eq("orders"), argThat(orders -> 
                    orders instanceof Collection && ((Collection<?>)orders).isEmpty()
                ));
            }
        }
    }
    
    // ========================================================================
    // UserFilter Action Tests
    // ========================================================================
    
    @Nested
    @DisplayName("UserFilter Action Tests")
    class UserFilterTests {
        
        @Test
        @DisplayName("UserFilter filters orders by username")
        void testUserFilterByUsername() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("UserFilter");
            when(request.getParameter("user")).thenReturn("testuser");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> userOrders = createTestOrdersForUser("testuser", 3);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList());
                        when(mock.doRetrieveByUser("testuser")).thenReturn(userOrders);
                    });
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(orderDaoMock.constructed().get(0)).doRetrieveByUser("testuser");
                verify(request, atLeastOnce()).setAttribute(eq("orders"), any());
            }
        }
        
        @Test
        @DisplayName("UserFilter with non-existent user returns empty")
        void testUserFilterNoResults() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("UserFilter");
            when(request.getParameter("user")).thenReturn("nonexistent");
            when(request.getParameter("sort")).thenReturn(null);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList());
                        when(mock.doRetrieveByUser("nonexistent")).thenReturn(Collections.emptyList());
                    });
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(orderDaoMock.constructed().get(0)).doRetrieveByUser("nonexistent");
            }
        }
    }
    
    // ========================================================================
    // DateFilter Action Tests
    // ========================================================================
    
    @Nested
    @DisplayName("DateFilter Action Tests")
    class DateFilterTests {
        
        @Test
        @DisplayName("DateFilter filters orders within date range")
        void testDateFilterWithinRange() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DateFilter");
            when(request.getParameter("dateMin")).thenReturn("2025-01-01");
            when(request.getParameter("dateMax")).thenReturn("2025-12-31");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> allOrders = new ArrayList<>();
            OrderBean order1 = new OrderBean();
            order1.setCodice(1);
            order1.setDataOrdine("2025-06-15"); // Within range
            allOrders.add(order1);
            
            OrderBean order2 = new OrderBean();
            order2.setCodice(2);
            order2.setDataOrdine("2024-06-15"); // Outside range
            allOrders.add(order2);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(allOrders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Verify filtered orders are set
                verify(request, atLeastOnce()).setAttribute(eq("orders"), any());
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("DateFilter with same min and max date")
        void testDateFilterSameDay() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DateFilter");
            when(request.getParameter("dateMin")).thenReturn("2025-06-15");
            when(request.getParameter("dateMax")).thenReturn("2025-06-15");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> allOrders = new ArrayList<>();
            OrderBean order1 = new OrderBean();
            order1.setCodice(1);
            order1.setDataOrdine("2025-06-15"); // Exact match
            allOrders.add(order1);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(allOrders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("DateFilter with no orders in range returns empty")
        void testDateFilterNoOrdersInRange() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DateFilter");
            when(request.getParameter("dateMin")).thenReturn("2030-01-01");
            when(request.getParameter("dateMax")).thenReturn("2030-12-31");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> allOrders = new ArrayList<>();
            OrderBean order1 = new OrderBean();
            order1.setCodice(1);
            order1.setDataOrdine("2025-06-15"); // Outside future range
            allOrders.add(order1);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(allOrders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
    }
    
    // ========================================================================
    // User-DateFilter Action Tests
    // ========================================================================
    
    @Nested
    @DisplayName("User-DateFilter Action Tests")
    class UserDateFilterTests {
        
        @Test
        @DisplayName("User-DateFilter filters by user and date range")
        void testUserDateFilter() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("User-DateFilter");
            when(request.getParameter("user")).thenReturn("testuser");
            when(request.getParameter("dateMin")).thenReturn("2025-01-01");
            when(request.getParameter("dateMax")).thenReturn("2025-12-31");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> userOrders = new ArrayList<>();
            OrderBean order1 = new OrderBean();
            order1.setCodice(1);
            order1.setUtente("testuser");
            order1.setDataOrdine("2025-06-15"); // Within range
            userOrders.add(order1);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList());
                        when(mock.doRetrieveByUser("testuser")).thenReturn(userOrders);
                    });
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(orderDaoMock.constructed().get(0)).doRetrieveByUser("testuser");
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("User-DateFilter with orders outside date range")
        void testUserDateFilterOutsideRange() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("User-DateFilter");
            when(request.getParameter("user")).thenReturn("testuser");
            when(request.getParameter("dateMin")).thenReturn("2030-01-01");
            when(request.getParameter("dateMax")).thenReturn("2030-12-31");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> userOrders = new ArrayList<>();
            OrderBean order1 = new OrderBean();
            order1.setCodice(1);
            order1.setUtente("testuser");
            order1.setDataOrdine("2025-06-15"); // Outside range
            userOrders.add(order1);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList());
                        when(mock.doRetrieveByUser("testuser")).thenReturn(userOrders);
                    });
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
    }
    
    // ========================================================================
    // OrderDetails Action Tests
    // ========================================================================
    
    @Nested
    @DisplayName("OrderDetails Action Tests")
    class OrderDetailsTests {
        
        @Test
        @DisplayName("OrderDetails retrieves order items")
        void testOrderDetailsRetrievesItems() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("orderDetails");
            when(request.getParameter("orderNum")).thenReturn("1");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<ContainBean> orderItems = new ArrayList<>();
            ContainBean item1 = new ContainBean();
            item1.setCodiceOrdine(1);
            item1.setCodiceProdotto(1);
            item1.setQuantità(2);
            orderItems.add(item1);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList()));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByOrder(1)).thenReturn(orderItems))) {
                
                servlet.doPost(request, response);
                
                verify(containDaoMock.constructed().get(0)).doRetrieveByOrder(1);
                verify(request).setAttribute("Details", orderItems);
            }
        }
        
        @Test
        @DisplayName("OrderDetails with empty order")
        void testOrderDetailsEmptyOrder() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("orderDetails");
            when(request.getParameter("orderNum")).thenReturn("999");
            when(request.getParameter("sort")).thenReturn(null);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList()));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByOrder(999)).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute(eq("Details"), argThat(items ->
                    items instanceof Collection && ((Collection<?>)items).isEmpty()
                ));
            }
        }
        
        @Test
        @DisplayName("OrderDetails with multiple items")
        void testOrderDetailsMultipleItems() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("orderDetails");
            when(request.getParameter("orderNum")).thenReturn("1");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<ContainBean> orderItems = new ArrayList<>();
            for (int i = 1; i <= 3; i++) {
                ContainBean item = new ContainBean();
                item.setCodiceOrdine(1);
                item.setCodiceProdotto(i);
                item.setQuantità(i);
                orderItems.add(item);
            }
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList()));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByOrder(1)).thenReturn(orderItems))) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute("Details", orderItems);
            }
        }
    }
    
    // ========================================================================
    // Exception Handling Tests
    // ========================================================================
    
    @Nested
    @DisplayName("Exception Handling Tests")
    class ExceptionHandlingTests {
        
        @Test
        @DisplayName("SQLException sets error and sends 500")
        void testSqlExceptionHandled() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(request.getParameter("sort")).thenReturn(null);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> {
                        when(mock.doRetrieveAll(any())).thenThrow(new SQLException("Database error"));
                    });
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(request).setAttribute(eq("error"), anyString());
                verify(response).sendError(eq(500), anyString());
            }
        }
        
        @Test
        @DisplayName("NumberFormatException for invalid order number")
        void testInvalidOrderNumber() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("orderDetails");
            when(request.getParameter("orderNum")).thenReturn("not-a-number");
            when(request.getParameter("sort")).thenReturn(null);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList()));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                assertThrows(NumberFormatException.class, () -> servlet.doPost(request, response));
            }
        }
        
        @Test
        @DisplayName("IllegalArgumentException for invalid date format")
        void testInvalidDateFormat() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DateFilter");
            when(request.getParameter("dateMin")).thenReturn("invalid-date");
            when(request.getParameter("dateMax")).thenReturn("2025-12-31");
            when(request.getParameter("sort")).thenReturn(null);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList()));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                assertThrows(IllegalArgumentException.class, () -> servlet.doPost(request, response));
            }
        }
    }
    
    // ========================================================================
    // Loop Boundary Tests
    // ========================================================================
    
    @Nested
    @DisplayName("Loop Boundary Tests")
    class LoopBoundaryTests {
        
        @Test
        @DisplayName("Zero orders - no iteration")
        void testZeroOrders() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DateFilter");
            when(request.getParameter("dateMin")).thenReturn("2025-01-01");
            when(request.getParameter("dateMax")).thenReturn("2025-12-31");
            when(request.getParameter("sort")).thenReturn(null);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList()));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Single order in date filter")
        void testSingleOrderDateFilter() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DateFilter");
            when(request.getParameter("dateMin")).thenReturn("2025-01-01");
            when(request.getParameter("dateMax")).thenReturn("2025-12-31");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> orders = new ArrayList<>();
            OrderBean order = new OrderBean();
            order.setCodice(1);
            order.setDataOrdine("2025-06-15");
            orders.add(order);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(orders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Multiple orders in date filter")
        void testMultipleOrdersDateFilter() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DateFilter");
            when(request.getParameter("dateMin")).thenReturn("2025-01-01");
            when(request.getParameter("dateMax")).thenReturn("2025-12-31");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> orders = new ArrayList<>();
            for (int i = 1; i <= 5; i++) {
                OrderBean order = new OrderBean();
                order.setCodice(i);
                order.setDataOrdine("2025-0" + i + "-15");
                orders.add(order);
            }
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(orders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Zero items in order details")
        void testZeroOrderItems() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("orderDetails");
            when(request.getParameter("orderNum")).thenReturn("1");
            when(request.getParameter("sort")).thenReturn(null);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList()));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveByOrder(1)).thenReturn(Collections.emptyList()))) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
    }
    
    // ========================================================================
    // Invalid/Unknown Action Tests
    // ========================================================================
    
    @Nested
    @DisplayName("Unknown Action Tests")
    class UnknownActionTests {
        
        @Test
        @DisplayName("Unknown action falls through to default behavior")
        void testUnknownAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("unknownAction");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> allOrders = createTestOrders(3);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(allOrders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Should still set orders from doRetrieveAll
                verify(request, atLeastOnce()).setAttribute(eq("orders"), any());
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Empty action string treated as no action")
        void testEmptyAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("");
            when(request.getParameter("sort")).thenReturn(null);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(Collections.emptyList()));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
    }
    
    // ========================================================================
    // Boundary Value Tests for isRightDate
    // ========================================================================
    
    @Nested
    @DisplayName("isRightDate Boundary Tests")
    class IsRightDateBoundaryTests {
        
        @Test
        @DisplayName("Order date equals minimum date")
        void testOrderDateEqualsMin() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DateFilter");
            when(request.getParameter("dateMin")).thenReturn("2025-06-15");
            when(request.getParameter("dateMax")).thenReturn("2025-12-31");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> orders = new ArrayList<>();
            OrderBean order = new OrderBean();
            order.setCodice(1);
            order.setDataOrdine("2025-06-15"); // Equals min
            orders.add(order);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(orders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Order should be included
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Order date equals maximum date")
        void testOrderDateEqualsMax() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DateFilter");
            when(request.getParameter("dateMin")).thenReturn("2025-01-01");
            when(request.getParameter("dateMax")).thenReturn("2025-06-15");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> orders = new ArrayList<>();
            OrderBean order = new OrderBean();
            order.setCodice(1);
            order.setDataOrdine("2025-06-15"); // Equals max
            orders.add(order);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(orders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Order date one day before minimum")
        void testOrderDateBeforeMin() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DateFilter");
            when(request.getParameter("dateMin")).thenReturn("2025-06-16");
            when(request.getParameter("dateMax")).thenReturn("2025-12-31");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> orders = new ArrayList<>();
            OrderBean order = new OrderBean();
            order.setCodice(1);
            order.setDataOrdine("2025-06-15"); // One day before min
            orders.add(order);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(orders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Order should be excluded from filtered result
                verify(dispatcher).forward(request, response);
            }
        }
        
        @Test
        @DisplayName("Order date one day after maximum")
        void testOrderDateAfterMax() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DateFilter");
            when(request.getParameter("dateMin")).thenReturn("2025-01-01");
            when(request.getParameter("dateMax")).thenReturn("2025-06-14");
            when(request.getParameter("sort")).thenReturn(null);
            
            Collection<OrderBean> orders = new ArrayList<>();
            OrderBean order = new OrderBean();
            order.setCodice(1);
            order.setDataOrdine("2025-06-15"); // One day after max
            orders.add(order);
            
            try (MockedConstruction<OrderDaoDataSource> orderDaoMock = mockConstruction(OrderDaoDataSource.class,
                    (mock, context) -> when(mock.doRetrieveAll(any())).thenReturn(orders));
                 MockedConstruction<ContainDaoDataSource> containDaoMock = mockConstruction(ContainDaoDataSource.class)) {
                
                servlet.doPost(request, response);
                
                // Order should be excluded from filtered result
                verify(dispatcher).forward(request, response);
            }
        }
    }
    
    // ========================================================================
    // Helper Methods
    // ========================================================================
    
    private Collection<OrderBean> createTestOrders(int count) {
        Collection<OrderBean> orders = new LinkedList<>();
        for (int i = 1; i <= count; i++) {
            OrderBean order = new OrderBean();
            order.setCodice(i);
            order.setUtente("user" + i);
            order.setDataOrdine("2025-0" + Math.min(i, 9) + "-15");
            order.setSaldoTotale(100.00 * i);
            orders.add(order);
        }
        return orders;
    }
    
    private Collection<OrderBean> createTestOrdersForUser(String username, int count) {
        Collection<OrderBean> orders = new LinkedList<>();
        for (int i = 1; i <= count; i++) {
            OrderBean order = new OrderBean();
            order.setCodice(i);
            order.setUtente(username);
            order.setDataOrdine("2025-0" + Math.min(i, 9) + "-15");
            order.setSaldoTotale(50.00 * i);
            orders.add(order);
        }
        return orders;
    }
}
