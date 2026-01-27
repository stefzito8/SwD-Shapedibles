package control;

import model.bean.UserBean;
import model.dao.IUserDao;
import model.datasource.UserDaoDataSource;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.sql.DataSource;
import java.io.IOException;
import java.sql.SQLException;

/**
 * Servlet implementation class AccountManage
 */
@WebServlet("/Users")
public class AccountManage extends HttpServlet {
	private static final long serialVersionUID = 1L;
       
    /**
     * @see HttpServlet#HttpServlet()
     */
    public AccountManage() {
        super();
    }

	/**
	 * @see HttpServlet#doGet(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		doPost(request,response);
	}

	/**
	 * @see HttpServlet#doPost(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		IUserDao userDao = null;
		
		DataSource ds= (DataSource) getServletContext().getAttribute("DataSource");
		userDao = createUserDao(ds);
		
		String action = request.getParameter("action");
		
		try {
			if(action != null){
				if(action.equalsIgnoreCase("admin")) {
					UserBean bean;
					String username = request.getParameter("username");
					bean = userDao.doRetrieveByKey(username);
					bean.setUserAdmin(1);
					userDao.doDelete(bean.getUsername());
					userDao.doSave(bean);
				} else if(action.equalsIgnoreCase("delete")) {
					String username = request.getParameter("username");
					userDao.doDelete(username);
				}
			}
			
			} catch(SQLException e) {
				request.setAttribute("error",  "Error: c'è stato un errore nel elaborazione degli utenti.");
		 		response.sendError(500, "Error: " + e.getMessage());
			}
		
		
		try {
			request.removeAttribute("users");
			request.setAttribute("users", userDao.doRetrieveAll(""));
		} catch (SQLException e) {
			request.setAttribute("error",  "Error: c'è stato un errore nel recupero dei dati degli utenti.");
	 		response.sendError(500, "Error: " + e.getMessage());
		}
		
		RequestDispatcher dispatcher = getServletContext().getRequestDispatcher("/WEB-INF/jsp/admin/accountManagement.jsp");
		dispatcher.forward(request, response);
	}

	/**
	 * Factory method for creating UserDao. Can be overridden for testing.
	 * @param ds DataSource to use
	 * @return IUserDao implementation
	 */
	protected IUserDao createUserDao(DataSource ds) {
		return new UserDaoDataSource(ds);
	}
}
