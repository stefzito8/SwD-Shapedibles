package control;

import model.dao.IInfoDao;
import model.dao.INutritionTableDao;
import model.dao.IProductDao;
import model.datasource.InfoDaoDataSource;
import model.datasource.NutritionTableDaoDataSource;
import model.datasource.ProductDaoDataSource;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.sql.DataSource;
import java.io.IOException;
import java.io.Serial;
import java.sql.SQLException;

public class Home extends HttpServlet {
    @Serial
    private static final long serialVersionUID = 1L;

    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doPost(request, response);
    }

    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        DataSource ds = (DataSource) getServletContext().getAttribute("DataSource");

        IProductDao prodDao = createProductDao(ds);
        IInfoDao infoDao = createInfoDao(ds);
        INutritionTableDao nutDao = createNutritionTableDao(ds);

        try {
            request.setAttribute("products", prodDao.doRetrieveAll("code"));
        } catch (SQLException e) {
            request.setAttribute("error",  "Error: c'è stato un problema con il recupero dati dei prodotti.");
            response.sendError(500, "Error: " + e.getMessage());
            System.out.println("Error..." + e.getMessage());
        }

        request.getRequestDispatcher("/WEB-INF/jsp/pages/home.jsp").forward(request, response);
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
