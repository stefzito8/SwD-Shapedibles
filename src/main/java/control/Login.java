package control;

import com.google.gson.Gson;
import model.bean.UserBean;
import model.dao.IUserDao;
import model.datasource.UserDaoDataSource;

import javax.servlet.ServletException;
import javax.servlet.annotation.MultipartConfig;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.servlet.http.HttpSession;
import javax.sql.DataSource;
import java.io.IOException;
import java.io.Serial;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.sql.SQLException;

/**
 * Servlet implementation class Login
 */
@WebServlet("/Login")
@MultipartConfig
public class Login extends HttpServlet {
	@Serial
	private static final long serialVersionUID = 1L;
       
    /**
     * @see HttpServlet#HttpServlet()
     */
    public Login() {
        super();
    }

	/**
	 * @see HttpServlet#doGet(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		//Make doGet dispatch the user to the loginView page
		request.getRequestDispatcher("/WEB-INF/jsp/pages/loginView.jsp").forward(request, response);
	}

	/**
	 * @see HttpServlet#doPost(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		boolean ajax = "XMLHttpRequest".equals(request.getHeader("X-Requested-With"));
		String username= request.getParameter("username");
		String password= request.getParameter("password");

		String redirectURL = request.getContextPath() + "/Login";
		
		UserBean userCheck;
		
		try {
			
			DataSource ds= (DataSource) getServletContext().getAttribute("DataSource");
			IUserDao userDao = createUserDao(ds);
			
			userCheck= userDao.doRetrieveByKey(username);
			
			if(username.equals(userCheck.getUsername()) && hashPassword(password).equals(userCheck.getPass())) 
			{
				HttpSession session = request.getSession(true);
				session.setAttribute("LoggedUser", userCheck);
				redirectURL = (String) session.getAttribute("redirectURL");
				if(redirectURL != null) {
					session.removeAttribute("redirectURL");
					
				} else {
					// Default redirect if no stored URL
					redirectURL = request.getContextPath() + "/Home";
				}
				
			}
			 else redirectURL = request.getContextPath() + "/Login";
			
		}
		catch(SQLException e)
		{
			request.setAttribute("error",  "Error: c'è stato un errore nel autentificazione, assicurarsi di inserire i campi corretamente.");
	 		response.sendError(500, "Error: " + e.getMessage());
		}
		catch(NoSuchAlgorithmException e)
		{
			request.setAttribute("error",  "Error: sembra esserci un problema con il login, se persiste contattare l'assistenza.");
	 		response.sendError(500, "Error: " + e.getMessage());System.out.println("Error..." + e.getMessage());
		}
		
		if(ajax) {
			response.setContentType("application/json");
			response.setCharacterEncoding("UTF-8");
			Gson gson = new Gson();
			if (redirectURL.equals(request.getContextPath() + "/Login"))
				response.setStatus(401);
			response.getWriter().write(gson.toJson(redirectURL));
		}
		else 
			response.sendRedirect(redirectURL);
	}

	private String hashPassword(String password) throws NoSuchAlgorithmException {
	    MessageDigest md = MessageDigest.getInstance("SHA-512");
	    byte[] hashedBytes = md.digest(password.getBytes(StandardCharsets.UTF_8));
	    StringBuilder sb = new StringBuilder();
	    for (byte b : hashedBytes) {
	        sb.append(String.format("%02x", b));
	    }
	    return sb.toString();
	   }

	protected IUserDao createUserDao(DataSource ds) {
        return new UserDaoDataSource(ds);
    }
}
