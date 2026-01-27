package filter;

import model.bean.UserBean;

import javax.servlet.*;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import java.io.IOException;

public class AuthenticationFilter implements Filter {

    @Override
    public void init(FilterConfig filterConfig) throws ServletException {
        // Initialization code, if needed
    }

    @Override
    public void doFilter(ServletRequest request, ServletResponse response, FilterChain chain)
            throws IOException, ServletException {
        HttpServletRequest httpRequest = (HttpServletRequest) request;
        HttpServletResponse httpResponse = (HttpServletResponse) response;
        HttpSession session = httpRequest.getSession(false);

        boolean isLoggedIn = (session != null && session.getAttribute("LoggedUser") != null);
        String loginURI = httpRequest.getContextPath() + "/Login";
        boolean isLoginRequest = httpRequest.getRequestURI().equals(loginURI);
        boolean isLoginPage = httpRequest.getRequestURI().endsWith("loginView.jsp");

        if (isLoggedIn || isLoginRequest || isLoginPage) {
            if (isLoggedIn && httpRequest.getRequestURI().contains("/admin/")) {
                UserBean user = (UserBean) session.getAttribute("LoggedUser");
                if (user.getUserAdmin() != 1) {
                    httpResponse.sendRedirect(httpRequest.getContextPath() + "/Home");
                    return;
                }
            }
            chain.doFilter(request, response);
        } else {
            // FIX: Validazione dell'input prima di metterlo in sessione
            String requestURI = httpRequest.getRequestURI();
            String contextPath = httpRequest.getContextPath();

            // Controllo di nullità
            // Controllo che l'URI inizi con il context path della nostra app (evita redirect esterni)
            if (requestURI != null && requestURI.startsWith(contextPath)) {
                
                // Rimuove eventuali caratteri di a capo (CRLF) 
                // per evitare log injection o corruzione degli header se usato successivamente
                String safeURI = requestURI.replaceAll("[\r\n]", "");
                
                session = httpRequest.getSession();
                session.setAttribute("redirectURL", safeURI);
            }
            httpResponse.sendRedirect(loginURI);
        }
    }

    // init() and destroy() methods as before
}