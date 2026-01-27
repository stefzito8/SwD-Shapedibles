package control;

import model.bean.InfoBean;
import model.bean.NutritionTableBean;
import model.bean.ProductBean;
import model.dao.IInfoDao;
import model.dao.INutritionTableDao;
import model.dao.IProductDao;
import model.datasource.InfoDaoDataSource;
import model.datasource.NutritionTableDaoDataSource;
import model.datasource.ProductDaoDataSource;

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
 * Servlet implementation class ProductDetails
 */
@WebServlet("/ProductDetails")
public class ProductDetails extends HttpServlet {
	@Serial
	private static final long serialVersionUID = 1L;
       
    /**
     * @see HttpServlet#HttpServlet()
     */
    public ProductDetails() {
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
		IProductDao prodDao = null;
		IInfoDao infoDao = null;
		INutritionTableDao nutDao= null;
		DataSource ds = (DataSource) getServletContext().getAttribute("DataSource");
		prodDao= createProductDao(ds);
		infoDao= createInfoDao(ds);
		nutDao = createNutritionTableDao(ds);
		
		try {
			ProductBean product= prodDao.doRetrieveByKey(Integer.parseInt(request.getParameter("product"))) ;
			InfoBean info = infoDao.doRetrieveByKey(product.getInfoCorrenti());
			NutritionTableBean nutritionTable = nutDao.doRetrieveByKey(product.getCodice());
			
			
			request.removeAttribute("product");
			request.setAttribute("product", product);
			request.removeAttribute("info");
			request.setAttribute("info", info);
			request.removeAttribute("nutritionTable");
			request.setAttribute("nutritionTable", nutritionTable);
			
		} catch(SQLException e) 
		{
			request.setAttribute("error",  "Error: c'è stato un problema con il recupero dati del prodotto.");
	 		response.sendError(500, "Error: " + e.getMessage());System.out.println("Error..." + e.getMessage());
		}
		
		RequestDispatcher dispatcher = getServletContext().getRequestDispatcher("/WEB-INF/jsp/pages/productDetails.jsp");
		dispatcher.forward(request, response);
	}

	/**
	 * Factory method for ProductDao - can be overridden in tests.
	 */
	protected IProductDao createProductDao(DataSource ds) {
		return new ProductDaoDataSource(ds);
	}

	/**
	 * Factory method for InfoDao - can be overridden in tests.
	 */
	protected IInfoDao createInfoDao(DataSource ds) {
		return new InfoDaoDataSource(ds);
	}

	/**
	 * Factory method for NutritionTableDao - can be overridden in tests.
	 */
	protected INutritionTableDao createNutritionTableDao(DataSource ds) {
		return new NutritionTableDaoDataSource(ds);
	}

}
