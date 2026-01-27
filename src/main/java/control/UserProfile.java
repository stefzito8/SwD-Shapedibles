package control;

import model.bean.ContainBean;
import model.bean.OrderBean;
import model.bean.UserBean;
import model.dao.IContainDao;
import model.dao.IOrderDao;
import model.dao.IUserDao;
import model.datasource.ContainDaoDataSource;
import model.datasource.OrderDaoDataSource;
import model.datasource.UserDaoDataSource;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.sql.DataSource;
import java.io.IOException;
import java.io.Serial;
import java.sql.SQLException;
import java.util.Collection;

/**
 * Servlet implementation class UserProfile
 */
@WebServlet("/UserProfile")
public class UserProfile extends HttpServlet {
	@Serial
	private static final long serialVersionUID = 1L;
       
    /**
     * @see HttpServlet#HttpServlet()
     */
    public UserProfile() {
        super();
    }

	/**
	 * @see HttpServlet#doGet(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
		doPost(request, response);
	}

	/**
	 * @see HttpServlet#doPost(HttpServletRequest request, HttpServletResponse response)
	 */
	protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        IUserDao userDao = null;
		IOrderDao orderDao = null;
		IContainDao containDao = null;
		
		DataSource ds= (DataSource) getServletContext().getAttribute("DataSource");
		userDao = createUserDao(ds);
		orderDao = createOrderDao(ds);
		containDao= createContainDao(ds);
		
		String action = request.getParameter("action");
		UserBean user = (UserBean) request.getSession().getAttribute("LoggedUser");
		
		if(user==null) {request.setAttribute("error", "Errore: Non c'è alcun utente loggato");}
		
		try {
			
			
			Collection<OrderBean> ordini =  orderDao.doRetrieveByUser(user.getUsername());
			
			if(action != null){
				if(action.equalsIgnoreCase("orderDetails")) {
					int orderNum = Integer.parseInt(request.getParameter("orderNum"));
					String orderUser = request.getParameter("orderUser");
					Collection<ContainBean> items = containDao.doRetrieveByOrder(orderNum);
					request.removeAttribute("Details");
					request.setAttribute("Details", items);
				}
			}
			} catch(SQLException e) {
				request.setAttribute("error",  "Error: c'è stato un errore nel elaborazione dei tuoi dati.");
		 		response.sendError(500, "Error: " + e.getMessage());
			}
		
		
		try {
			request.removeAttribute("OrdersLoggedUser");
			request.setAttribute("OrdersLoggedUser", orderDao.doRetrieveByUser(user.getUsername()));
		} catch (SQLException e) {
			request.setAttribute("error",  "Error: c'è stato un errore nel recupero delle informazioni del profilo utente.");
	 		response.sendError(500, "Error: " + e.getMessage());
		}
		
		RequestDispatcher dispatcher = getServletContext().getRequestDispatcher("/WEB-INF/jsp/pages/userProfile.jsp");
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

	/**
	 * Factory method for creating OrderDao. Can be overridden for testing.
	 * @param ds DataSource to use
	 * @return IOrderDao implementation
	 */
	protected IOrderDao createOrderDao(DataSource ds) {
		return new OrderDaoDataSource(ds);
	}

	/**
	 * Factory method for creating ContainDao. Can be overridden for testing.
	 * @param ds DataSource to use
	 * @return IContainDao implementation
	 */
	protected IContainDao createContainDao(DataSource ds) {
		return new ContainDaoDataSource(ds);
	}
}
