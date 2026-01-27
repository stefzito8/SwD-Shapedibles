package control;

import org.mockito.ArgumentCaptor;
import org.mockito.InOrder;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Utility methods for controller tests to help kill common mutations.
 * 
 * The key insight is that mutations like "removed call to setAttribute" 
 * or "removed call to sendError" survive when tests don't verify that 
 * the side effect's value/occurrence affects the test outcome.
 * 
 * These utility methods verify BOTH the side effect occurred AND that 
 * the content matches expectations.
 */
public class ControllerTestUtils {

    /**
     * Verifies error handling pattern that kills setAttribute and sendError mutations.
     * 
     * @param request The mocked request
     * @param response The mocked response
     * @param expectedErrorContains A substring expected in the error attribute (can be null)
     * @param expectedStatusCode The expected HTTP status code (usually 500)
     * @throws Exception if verification fails
     */
    public static void verifyErrorHandling(
            HttpServletRequest request, 
            HttpServletResponse response,
            String expectedErrorContains,
            int expectedStatusCode) throws Exception {
        
        // Capture error attribute
        ArgumentCaptor<String> errorCaptor = ArgumentCaptor.forClass(String.class);
        verify(request).setAttribute(eq("error"), errorCaptor.capture());
        
        String actualError = errorCaptor.getValue();
        assertNotNull(actualError, "Error attribute should not be null");
        assertTrue(actualError.contains("Error:"), "Error should contain 'Error:' prefix");
        if (expectedErrorContains != null) {
            assertTrue(actualError.contains(expectedErrorContains), 
                "Error should contain: " + expectedErrorContains);
        }
        
        // Verify sendError with status code
        verify(response).sendError(eq(expectedStatusCode), anyString());
    }

    /**
     * Verifies that error attribute AND response are consistent,
     * with proper ordering (setAttribute before sendError).
     * 
     * @param request The mocked request
     * @param response The mocked response
     * @param expectedExceptionMessage A substring expected in the sendError message
     * @throws Exception if verification fails
     */
    public static void verifyCompleteErrorFlow(
            HttpServletRequest request,
            HttpServletResponse response,
            String expectedExceptionMessage) throws Exception {
        
        // InOrder ensures setAttribute happens before sendError
        InOrder inOrder = inOrder(request, response);
        inOrder.verify(request).setAttribute(eq("error"), argThat(msg -> 
            msg != null && msg.toString().contains("Error:")
        ));
        inOrder.verify(response).sendError(eq(500), contains(expectedExceptionMessage));
    }

    /**
     * Verifies that a specific error attribute message was set.
     * 
     * @param request The mocked request
     * @param expectedExactMessage The exact expected error message
     * @throws Exception if verification fails
     */
    public static void verifyExactErrorAttribute(
            HttpServletRequest request,
            String expectedExactMessage) throws Exception {
        
        verify(request).setAttribute(eq("error"), eq(expectedExactMessage));
    }

    /**
     * Verifies that sendError was called with the expected status code and message content.
     * 
     * @param response The mocked response
     * @param expectedStatusCode The expected HTTP status code
     * @param expectedMessageContains A substring expected in the error message
     * @throws Exception if verification fails
     */
    public static void verifySendErrorWithMessage(
            HttpServletResponse response,
            int expectedStatusCode,
            String expectedMessageContains) throws Exception {
        
        ArgumentCaptor<String> messageCaptor = ArgumentCaptor.forClass(String.class);
        verify(response).sendError(eq(expectedStatusCode), messageCaptor.capture());
        
        String actualMessage = messageCaptor.getValue();
        assertNotNull(actualMessage, "Error message should not be null");
        assertTrue(actualMessage.contains(expectedMessageContains),
            "Error message should contain: " + expectedMessageContains + 
            ", but was: " + actualMessage);
    }

    /**
     * Verifies that no request dispatcher was obtained after an error.
     * This is useful to ensure that after an exception, the normal forward doesn't happen.
     * 
     * @param request The mocked request
     * @throws Exception if verification fails
     */
    public static void verifyNoForwardAfterError(HttpServletRequest request) throws Exception {
        verify(request, never()).getRequestDispatcher(anyString());
    }
}
