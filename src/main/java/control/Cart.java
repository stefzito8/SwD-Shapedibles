package control;

import com.google.gson.Gson;
import model.dao.IProductDao;
import model.dao.IUserDao;
import model.datasource.ProductDaoDataSource;
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
import java.util.HashMap;
import java.util.Map;

/**
 * Servlet implementation class Cart
 */
@WebServlet("/Cart")
public class Cart extends HttpServlet {
	@Serial
	private static final long serialVersionUID = 1L;
       
    /**
     * @see HttpServlet#HttpServlet()
     */
    public Cart() {
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
		boolean ajax = "XMLHttpRequest".equals(request.getHeader("X-Requested-With"));
		System.out.println("ajax: " + ajax);
		Map<String, Object> responseData = new HashMap<>();
        IProductDao productDao;
		
		
		DataSource ds= (DataSource) getServletContext().getAttribute("DataSource");
		productDao = createProductDao(ds);

		model.Cart cart = (model.Cart) request.getSession().getAttribute("cart");
		if(cart == null) 
		{
			cart = new model.Cart();
			request.getSession().setAttribute("cart", cart);
		}
	
		try {
	    	String action = request.getParameter("action");
			if (action != null) {
				if (action.equalsIgnoreCase("addC")) {
					int id = Integer.parseInt(request.getParameter("id"));
					cart.addProduct(productDao.doRetrieveByKey(id));
				} else if (action.equalsIgnoreCase("deleteC")) {
					int id = Integer.parseInt(request.getParameter("id"));
					cart.deleteProduct(productDao.doRetrieveByKey(id));
				}
			}
		} catch(SQLException e) {
			request.setAttribute("error",  "Error: c'è stato un errore nel elaborazione del carrello.");
	 		response.sendError(500, "Error: " + e.getMessage());
		}

		responseData.put("cartSize", cart.getCartSize());
		request.getSession().setAttribute("cart", cart);
		
		if (ajax) {
			response.setContentType("application/json");
			response.setCharacterEncoding("UTF-8");
			response.getWriter().write(new Gson().toJson(responseData));
		}
		else {
			RequestDispatcher dispatcher = getServletContext().getRequestDispatcher("/WEB-INF/jsp/pages/cart.jsp");
			dispatcher.forward(request, response);
		}
	}

	protected IProductDao createProductDao(DataSource ds) {
        return new ProductDaoDataSource(ds);
    }
}
