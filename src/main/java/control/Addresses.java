package control;

import model.bean.AddressBean;
import model.bean.UserBean;
import model.dao.IAddressDao;
import model.dao.IUserDao;
import model.datasource.AddressDaoDataSource;
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

/**
 * Servlet implementation class AdressesControl
 */
@WebServlet("/addressesControl")
public class Addresses extends HttpServlet {
	@Serial
	private static final long serialVersionUID = 1L;
       
    /**
     * @see HttpServlet#HttpServlet()
     */
    public Addresses() {
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
		UserBean user = (UserBean) request.getSession().getAttribute("LoggedUser");
		IUserDao userDao = null;
		IAddressDao addressDao= null;
		DataSource ds= (DataSource) getServletContext().getAttribute("DataSource");
		userDao = new UserDaoDataSource(ds);
		addressDao= new AddressDaoDataSource(ds);
		
		 int max = 50;
	     int min = 1;
	     int range = max - min + 1;
	     int number= (int) (Math.random() * range) - min;
		
		String action = request.getParameter("action");
		
		try {
			if(action != null){
				if(action.equalsIgnoreCase("Add")) {
					AddressBean address = new AddressBean();
					address.setId("ad" + user.getUsername() +"-" + number);
					address.setUtente(user.getUsername());
					address.setPaese(request.getParameter("country"));
					address.setCittà(request.getParameter("city"));
					address.setStrada(request.getParameter("street"));
					address.setNumero(Integer.parseInt(request.getParameter("number")));
					address.setCodicePostale(request.getParameter("Postal_code"));
					
					addressDao.doSave(address);
				} else if(action.equalsIgnoreCase("delete")) {
					String id = request.getParameter("id");
					addressDao.doDelete(id, user.getUsername());
				}
			}
			
			} catch(SQLException e) {
				request.setAttribute("error",  "Error: c'è stato un errore nel elaborazione del degli indirizzi, assicurati di aver inserito corretamente eventuali dati.");
		 		response.sendError(500, "Error: " + e.getMessage());
			}
		
		
		try {
			request.removeAttribute("addresses");
			request.setAttribute("addresses", addressDao.doRetrieveByUser(user.getUsername()) );
		} catch (SQLException e) {
			request.setAttribute("error",  "Error: c'è stato un errore nel recupero degli indirizzi");
	 		response.sendError(500, "Error: " + e.getMessage());
		}
		
		RequestDispatcher dispatcher = getServletContext().getRequestDispatcher("/WEB-INF/jsp/pages/addresses.jsp");
		dispatcher.forward(request, response);
	}

}
