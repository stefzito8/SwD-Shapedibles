package control;

import model.Cart;
import model.bean.*;
import model.dao.*;
import model.datasource.*;

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
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Servlet implementation class Checkout
 */
@WebServlet("/Checkout")
public class Checkout extends HttpServlet {
	@Serial
	private static final long serialVersionUID = 1L;
	
	DateTimeFormatter dtf = DateTimeFormatter.ofPattern("yyyy-mm-dd");
	LocalDateTime now = LocalDateTime.now();
       
    /**
     * @see HttpServlet#HttpServlet()
     */
    public Checkout() {
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
		OrderBean bean = new OrderBean();
        Cart cart = (Cart) request.getSession().getAttribute("cart");
        UserBean user = (UserBean) request.getSession().getAttribute("LoggedUser");
	 	String action = request.getParameter("action");
	 	
	 	// Redirect to login if user is not authenticated
	 	if (user == null) {
	 		response.sendRedirect("Login");
	 		return;
	 	}
	 	
		DataSource ds= (DataSource) getServletContext().getAttribute("DataSource");
        IProductDao productDao = createProductDao(ds);
        IOrderDao orderDao = createOrderDao(ds);
        IAddressDao addressDao = createAddressDao(ds);
        IInfoDao infoDao = createInfoDao(ds);
        IContainDao containDao = createContainDao(ds); 
		
        int max = 10000;
        int min = 1;
        int range = max - min + 1;
				
		try {
			
			 Collection<AddressBean> addresses = addressDao.doRetrieveByUser(user.getUsername());
			
			 request.removeAttribute("addresses");
			 request.setAttribute("addresses", addresses);

			
				
				System.out.println(" username: " + user.getUsername());
				bean.setUtente(user.getUsername());
				bean.setStato("in checkout");
				bean.setDataOrdine(now.toString().substring(0,10));
				
	 	
				
					
				String address = request.getParameter("address");
				System.out.println(address);
				if(address !="" && address!= null) bean.setIndirizzo(address);
				
				if(bean.getIndirizzo()==" ") 
				{ 
					int codice=(int) (Math.random() * range) - min;
					bean.setCodice(codice);
					request.getSession().removeAttribute("order");
					request.getSession().setAttribute("order", bean);
					//System.out.println("codice:" + codice + " " + request.getAttribute("ordersCode") + " " +bean.getCodice());
				}
				else 
				{	
					OrderBean temp = (OrderBean) request.getSession().getAttribute("order");
					bean.setCodice(temp.getCodice());
				}
				
				double saldotot=0.0;
			 	
				List<ProductBean> prodcart = (List<ProductBean>) cart.getProducts();
				List<ContainBean> containList = new ArrayList<>();
					for(ProductBean beancart: prodcart) {
						    ContainBean contain= new ContainBean();
							InfoBean infob = infoDao.doRetrieveByKey(beancart.getCodice());
							saldotot += infob.getCosto() * cart.getProductQuantity(beancart);
							contain.setCodiceProdotto(beancart.getCodice());
							contain.setCodiceOrdine(bean.getCodice());
							contain.setQuantità(cart.getProductQuantity(beancart));
							containList.add(contain);
					}
				bean.setSaldoTotale(saldotot);	
				request.removeAttribute("order");
				request.setAttribute("order", bean);
			
				request.removeAttribute("containList");
				request.setAttribute("containList", containList);
				
				
				
					
				if(action != null){
					if(action.equalsIgnoreCase("confirm")) {
						bean.setStato("completato");
						orderDao.doSave(bean);	
						for(ContainBean conbean: containList) {
							InfoBean info= infoDao.doRetrieveByKey(conbean.getCodiceProdotto());
							ProductBean product = productDao.doRetrieveByName(info.getNome());
							infoDao.doUpdateQuantity(info.getCodice(),info.getDisponibilità() - cart.getProductQuantity(product));
							containDao.doSave(conbean);
						}
						cart.ClearCart();
		        }
			  }
		   
		   RequestDispatcher dispatcher = getServletContext().getRequestDispatcher("/WEB-INF/jsp/pages/checkout.jsp");
		   dispatcher.forward(request, response);
		  
		   
	 	} catch(SQLException e) 
	 	{
	 		request.setAttribute("error",  "Error: c'è stato un errore nel elaborazione del ordine, assicurarsi di inserire i campi corretamente.");
	 		response.sendError(500, "Error: " + e.getMessage());
	 		System.out.println("Error: " + e.getMessage());
	 	}
		   
	 	
	}

	/**
	 * Factory method for ProductDao - can be overridden in tests.
	 */
	protected IProductDao createProductDao(DataSource ds) {
		return new ProductDaoDataSource(ds);
	}

	/**
	 * Factory method for OrderDao - can be overridden in tests.
	 */
	protected IOrderDao createOrderDao(DataSource ds) {
		return new OrderDaoDataSource(ds);
	}

	/**
	 * Factory method for AddressDao - can be overridden in tests.
	 */
	protected IAddressDao createAddressDao(DataSource ds) {
		return new AddressDaoDataSource(ds);
	}

	/**
	 * Factory method for InfoDao - can be overridden in tests.
	 */
	protected IInfoDao createInfoDao(DataSource ds) {
		return new InfoDaoDataSource(ds);
	}

	/**
	 * Factory method for ContainDao - can be overridden in tests.
	 */
	protected IContainDao createContainDao(DataSource ds) {
		return new ContainDaoDataSource(ds);
	}

}
