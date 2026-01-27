package control;

import com.google.gson.Gson;
import model.bean.UserBean;
import model.dao.IUserDao;
import model.datasource.UserDaoDataSource;
import model.enums.Country;
import model.enums.Gender;

import javax.servlet.ServletException;
import javax.servlet.annotation.MultipartConfig;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.sql.DataSource;
import java.io.IOException;
import java.io.Serial;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.sql.SQLException;
import java.util.Collection;
import java.util.Iterator;

/**
 * Servlet implementation class Register
 */
@WebServlet("/Register")
@MultipartConfig
public class Register extends HttpServlet {
	@Serial
	private static final long serialVersionUID = 1L;
	
       
    /**
     * @see HttpServlet#HttpServlet()
     */
    public Register() {
        super();
    }

	/**
	 * @see HttpServlet#doGet(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		request.setAttribute("countries", Country.getValues());
		request.setAttribute("genders", Gender.getValues());
		//Make doGet dispatch the user to the loginView page
		request.getRequestDispatcher("/WEB-INF/jsp/pages/registerView.jsp").forward(request, response);
	}

	/**
	 * @see HttpServlet#doPost(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		request.setAttribute("countries", Country.getValues());
		request.setAttribute("genders", Gender.getValues());
		
		DataSource ds= (DataSource) getServletContext().getAttribute("DataSource");
		IUserDao userDao = createUserDao(ds);
		String error=null;
		boolean ajax = "XMLHttpRequest".equals(request.getHeader("X-Requested-With"));
		String username= request.getParameter("username");
		String email= request.getParameter("email");
		String password= request.getParameter("password");
		String passwordConf= request.getParameter("passwordConf");
		String nomeCognome= request.getParameter("name_surname");
		String sesso= request.getParameter("gender");
		String paese= request.getParameter("country");
		String dataNascista= request.getParameter("birthday");
		int isAdmin= 0;

		String redirectURL = request.getContextPath() + "/Login";
		
		try {
		
			UserBean user= new UserBean();
			System.out.println(checkUsername(username, userDao));
			if(checkUsername(username, userDao)==true) {
				if(password.equals(passwordConf)) 
				{
					user.setUsername(username);
					user.setEmail(email);
					user.setPass(hashPassword(password));
					user.setNomeCognome(nomeCognome);
					user.setSesso(sesso);
					user.setPaese(paese);
					user.setDataNascita(dataNascista);
					user.setUserAdmin(isAdmin);
			
				
					userDao.doSave(user);
				}
				else {
			    		error = "Le password non combaciano.";
			    		request.setAttribute("error", "Error: " + error);
			    		request.setAttribute("ajaxError", error);
			 		}
			}
		    else {
		    		error = "L'username scelto è già esistente";
		    		request.setAttribute("error", "Error: " + error);
		    		request.setAttribute("ajaxError", error);
		 		 }
			
				
		    }
			catch(SQLException e)
			{
				
				error = "C'è stato un errore nel salvataggio delle credenziali, assicurarsi di inserire i campi corretamente.";
				request.setAttribute("error", "Error: " + error);
				request.setAttribute("ajaxError", error);
		 		response.sendError(500, "Error: " + e.getMessage());
			}
			catch(NoSuchAlgorithmException e)
			{
				
				error = "Sembra esserci un problema con la registrazione, se persiste contattare l'assistenza.";
				request.setAttribute("error", "Error: " + error);
				request.setAttribute("ajaxError", error);
				response.sendError(500, "Error: " + e.getMessage());System.out.println("Error..." + e.getMessage());
			}
			
			

			if(ajax) {
				response.setContentType("application/json");
				response.setCharacterEncoding("UTF-8");
				Gson gson = new Gson();
				if (request.getAttribute("ajaxError") != null) {
					String ajaxError = request.getAttribute("ajaxError").toString();
					response.setStatus(401);
					response.getWriter().write(gson.toJson(ajaxError));
					
				}
				else
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
	
	private boolean checkUsername(String username, IUserDao userDao) throws SQLException 
	{
		Collection<?> userCheck = (Collection<?>) userDao.doRetrieveAll("");
		Iterator<?> it=  userCheck.iterator();
		while(it.hasNext()) 
		{
			UserBean bean= (UserBean) it.next();
			System.out.println(bean.getUsername());
			if(username.equals(bean.getUsername())) return false;
		} 
		return true;
	}

	/**
	 * Factory method for UserDao - can be overridden in tests.
	 */
	protected IUserDao createUserDao(DataSource ds) {
		return new UserDaoDataSource(ds);
	}
}
