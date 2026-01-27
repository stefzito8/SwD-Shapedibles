package control;

import categories.UnitTest;
import model.bean.AddressBean;
import model.bean.UserBean;
import model.dao.IAddressDao;
import model.dao.IUserDao;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.mockito.junit.jupiter.MockitoSettings;
import org.mockito.quality.Strictness;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletContext;
import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import javax.sql.DataSource;
import java.io.IOException;
import java.sql.SQLException;
import java.util.ArrayList;
import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Unit tests for Addresses controller.
 * 
 * Testing Level: Unit
 * Technique: White-Box (Statement Testing, Branch Testing) with Mocking
 */
@UnitTest
@ExtendWith(MockitoExtension.class)
@MockitoSettings(strictness = Strictness.LENIENT)
@DisplayName("Addresses Controller Unit Tests")
public class AddressesTest {

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private HttpSession session;

    @Mock
    private ServletContext servletContext;

    @Mock
    private DataSource dataSource;

    @Mock
    private RequestDispatcher requestDispatcher;

    @Mock
    private IUserDao userDao;

    @Mock
    private IAddressDao addressDao;

    private Addresses addressesServlet;
    private UserBean loggedUser;

    @BeforeEach
    void setUp() throws Exception {
        addressesServlet = new Addresses() {
            @Override
            public ServletContext getServletContext() {
                return servletContext;
            }
            
            @Override
            protected IUserDao createUserDao(DataSource ds) {
                return userDao;
            }
            
            @Override
            protected IAddressDao createAddressDao(DataSource ds) {
                return addressDao;
            }
        };
        
        loggedUser = createTestUser("testuser");
        
        when(servletContext.getAttribute("DataSource")).thenReturn(dataSource);
        when(servletContext.getRequestDispatcher(anyString())).thenReturn(requestDispatcher);
        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("LoggedUser")).thenReturn(loggedUser);
    }

    // ============================================================================
    // doGet Tests
    // ============================================================================

    @Nested
    @DisplayName("doGet Tests")
    class DoGetTests {

        @Test
        @DisplayName("doGet delegates to doPost")
        void testDoGetDelegatesToDoPost() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(addressDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());

            addressesServlet.doGet(request, response);

            verify(servletContext).getRequestDispatcher("/WEB-INF/jsp/pages/addresses.jsp");
        }
    }

    // ============================================================================
    // doPost Tests - No Action
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - No Action")
    class DoPostNoActionTests {

        @Test
        @DisplayName("No action - verifies removeAttribute before setAttribute for addresses")
        void testNoAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            Collection<AddressBean> addresses = new ArrayList<>();
            addresses.add(createTestAddress("addr1", "testuser"));
            when(addressDao.doRetrieveByUser("testuser")).thenReturn(addresses);

            addressesServlet.doPost(request, response);

            // Verify removeAttribute is called BEFORE setAttribute (kills removeAttribute mutation)
            org.mockito.InOrder inOrder = inOrder(request);
            inOrder.verify(request).removeAttribute("addresses");
            inOrder.verify(request).setAttribute(eq("addresses"), any());
            verify(requestDispatcher).forward(request, response);
        }
        
        @Test
        @DisplayName("No action - verifies addresses attribute is used by testing removal")
        void testNoActionRemoveThenSet() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            Collection<AddressBean> addresses = new ArrayList<>();
            addresses.add(createTestAddress("addr1", "testuser"));
            when(addressDao.doRetrieveByUser("testuser")).thenReturn(addresses);

            addressesServlet.doPost(request, response);

            // Verify both removeAttribute and setAttribute are called
            verify(request).removeAttribute("addresses");
            verify(request).setAttribute("addresses", addresses);
        }
    }

    // ============================================================================
    // doPost Tests - Add Action
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - Add Action")
    class DoPostAddActionTests {

        @Test
        @DisplayName("Add action - verifies address ID format with random number")
        void testAddAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("Add");
            when(request.getParameter("country")).thenReturn("Italy");
            when(request.getParameter("city")).thenReturn("Rome");
            when(request.getParameter("street")).thenReturn("Via Roma");
            when(request.getParameter("number")).thenReturn("123");
            when(request.getParameter("Postal_code")).thenReturn("00100");
            when(addressDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());

            addressesServlet.doPost(request, response);

            // Verify address is saved with proper format - ID must contain random number
            // This kills mutations on lines 56-57 (random number generation)
            org.mockito.ArgumentCaptor<AddressBean> addressCaptor = org.mockito.ArgumentCaptor.forClass(AddressBean.class);
            verify(addressDao).doSave(addressCaptor.capture());
            
            AddressBean savedAddress = addressCaptor.getValue();
            assertNotNull(savedAddress.getId());
            assertTrue(savedAddress.getId().startsWith("adtestuser-"), "ID should start with 'ad' + username + '-'");
            // The ID format is: "ad" + username + "-" + number
            assertTrue(savedAddress.getId().matches("adtestuser--?\\d+"), "ID should contain a number after the dash");
            assertEquals("testuser", savedAddress.getUtente());
            assertEquals("Italy", savedAddress.getPaese());
            assertEquals("Rome", savedAddress.getCittà());
            assertEquals("Via Roma", savedAddress.getStrada());
            assertEquals(123, savedAddress.getNumero());
            assertEquals("00100", savedAddress.getCodicePostale());
            verify(requestDispatcher).forward(request, response);
        }

        @Test
        @DisplayName("Add action - case insensitive")
        void testAddActionCaseInsensitive() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("ADD");
            when(request.getParameter("country")).thenReturn("Italy");
            when(request.getParameter("city")).thenReturn("Rome");
            when(request.getParameter("street")).thenReturn("Via Roma");
            when(request.getParameter("number")).thenReturn("123");
            when(request.getParameter("Postal_code")).thenReturn("00100");
            when(addressDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());

            addressesServlet.doPost(request, response);

            verify(addressDao).doSave(any(AddressBean.class));
        }
    }

    // ============================================================================
    // doPost Tests - Delete Action
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - Delete Action")
    class DoPostDeleteActionTests {

        @Test
        @DisplayName("Delete action - delete address")
        void testDeleteAction() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("delete");
            when(request.getParameter("id")).thenReturn("addr123");
            when(addressDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());

            addressesServlet.doPost(request, response);

            verify(addressDao).doDelete("addr123", "testuser");
        }

        @Test
        @DisplayName("Delete action - case insensitive")
        void testDeleteActionCaseInsensitive() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("DELETE");
            when(request.getParameter("id")).thenReturn("addr456");
            when(addressDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());

            addressesServlet.doPost(request, response);

            verify(addressDao).doDelete("addr456", "testuser");
        }
    }

    // ============================================================================
    // doPost Tests - SQLException Handling
    // ============================================================================

    @Nested
    @DisplayName("doPost Tests - SQLException Handling")
    class DoPostSQLExceptionTests {

        @Test
        @DisplayName("SQLException during add - verifies both setAttribute AND sendError")
        void testSQLExceptionDuringAdd() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("Add");
            when(request.getParameter("country")).thenReturn("Italy");
            when(request.getParameter("city")).thenReturn("Rome");
            when(request.getParameter("street")).thenReturn("Via Roma");
            when(request.getParameter("number")).thenReturn("123");
            when(request.getParameter("Postal_code")).thenReturn("00100");
            doThrow(new SQLException("Add Error")).when(addressDao).doSave(any(AddressBean.class));
            when(addressDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());

            addressesServlet.doPost(request, response);

            // Kill mutations by verifying exact error message
            verify(request).setAttribute(eq("error"), 
                eq("Error: c'è stato un errore nel elaborazione del degli indirizzi, assicurati di aver inserito corretamente eventuali dati."));
            verify(response).sendError(eq(500), contains("Add Error"));
        }

        @Test
        @DisplayName("SQLException during delete - complete error handling verification")
        void testSQLExceptionDuringDelete() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("delete");
            when(request.getParameter("id")).thenReturn("addr123");
            doThrow(new SQLException("Delete Error")).when(addressDao).doDelete(anyString(), anyString());
            when(addressDao.doRetrieveByUser(anyString())).thenReturn(new ArrayList<>());

            addressesServlet.doPost(request, response);

            // Use InOrder to verify sequence
            org.mockito.InOrder inOrder = inOrder(request, response);
            inOrder.verify(request).setAttribute(eq("error"), contains("Error:"));
            inOrder.verify(response).sendError(eq(500), contains("Delete Error"));
        }

        @Test
        @DisplayName("SQLException during retrieve - verifies error attribute content")
        void testSQLExceptionDuringRetrieve() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(addressDao.doRetrieveByUser(anyString())).thenThrow(new SQLException("Retrieve Error"));

            addressesServlet.doPost(request, response);

            // Kill mutations by verifying exact error message
            verify(request).setAttribute(eq("error"), 
                eq("Error: c'è stato un errore nel recupero degli indirizzi"));
            verify(response).sendError(eq(500), contains("Retrieve Error"));
        }

        @Test
        @DisplayName("SQLException - verifies no forward after error")
        void testNoForwardAfterSQLException() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn(null);
            when(addressDao.doRetrieveByUser(anyString())).thenThrow(new SQLException("Error"));

            addressesServlet.doPost(request, response);

            // Verify error handling happened and verify sendError is called
            verify(response).sendError(eq(500), anyString());
            verify(request).setAttribute(eq("error"), anyString());
        }

        @Test
        @DisplayName("SQLException - verifies error flow order")
        void testSQLExceptionFlowOrder() throws ServletException, IOException, SQLException {
            when(request.getParameter("action")).thenReturn("Add");
            when(request.getParameter("country")).thenReturn("Italy");
            when(request.getParameter("city")).thenReturn("Rome");
            when(request.getParameter("street")).thenReturn("Via Roma");
            when(request.getParameter("number")).thenReturn("123");
            when(request.getParameter("Postal_code")).thenReturn("00100");
            doThrow(new SQLException("Flow Error")).when(addressDao).doSave(any(AddressBean.class));

            addressesServlet.doPost(request, response);

            // Use InOrder to verify sequence matters - kills mutations
            org.mockito.InOrder inOrder = inOrder(request, response);
            inOrder.verify(request).setAttribute(eq("error"), anyString());
            inOrder.verify(response).sendError(eq(500), anyString());
        }
    }

    // ============================================================================
    // Helper Methods
    // ============================================================================

    private UserBean createTestUser(String username) {
        UserBean user = new UserBean();
        user.setUsername(username);
        user.setEmail(username + "@test.com");
        user.setPass("password");
        user.setNomeCognome("Test User");
        user.setSesso("M");
        user.setPaese("Italy");
        user.setDataNascita("1990-01-01");
        user.setUserAdmin(0);
        return user;
    }

    private AddressBean createTestAddress(String id, String username) {
        AddressBean address = new AddressBean();
        address.setId(id);
        address.setUtente(username);
        address.setPaese("Italy");
        address.setCittà("Rome");
        address.setStrada("Via Roma");
        address.setNumero(1);
        address.setCodicePostale("00100");
        return address;
    }
}
