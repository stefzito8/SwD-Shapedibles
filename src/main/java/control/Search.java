package control;

import com.google.gson.*;
import model.Cart;
import model.bean.ProductBean;
import model.dao.IInfoDao;
import model.dao.IProductDao;
import model.datasource.InfoDaoDataSource;
import model.datasource.ProductDaoDataSource;

import javax.servlet.RequestDispatcher;
import javax.servlet.ServletException;
import javax.servlet.annotation.WebServlet;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;
import javax.sql.DataSource;
import java.io.IOException;
import java.lang.reflect.Type;
import java.sql.SQLException;
import java.util.Collection;

@WebServlet("/search")
public class Search extends HttpServlet {
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        String query = request.getParameter("ricerca");
        String id = request.getParameter("id");
        DataSource ds = (DataSource) getServletContext().getAttribute("DataSource");
        IProductDao productDao = createProductDao(ds);
        IInfoDao infoDao = createInfoDao(ds);

        try {
            Cart cart = (Cart) request.getSession().getAttribute("cart");
            if(cart == null)
            {
                cart = new Cart();
                request.getSession().setAttribute("cart", cart);
            }
            
            if (id != null) {
                ProductBean product = productDao.doRetrieveByKey(Integer.parseInt(id));
                if (product != null) {
                    response.setContentType("application/json");
                    response.setCharacterEncoding("UTF-8");
                    Gson gson = new GsonBuilder()
                            .registerTypeAdapter(ProductBean.class, new SingleProductBeanSerializer(cart, infoDao))
                            .create();
                    String json = gson.toJson(product);
                    response.getWriter().write(json);
                    return;
                }
            }
            
            Collection<ProductBean> searchResults = productDao.searchByName(query);

            // Controllo se la richiesta è di tipo AJAX
            boolean ajax = "XMLHttpRequest".equals(request.getHeader("X-Requested-With"));
            if (ajax) {
                response.setContentType("application/json");
                response.setCharacterEncoding("UTF-8");
                Gson gson = new GsonBuilder()
                        .registerTypeAdapter(searchResults.getClass(), new ProductBeanWithCartQuantity(cart, infoDao))
                        .create();
                String json = gson.toJson(searchResults);
                response.getWriter().write(json);
            } else {
                request.setAttribute("searchResults", searchResults);
                RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/jsp/pages/searchResults.jsp");
                dispatcher.forward(request, response);
            }
        } catch (SQLException e) {
            request.setAttribute("error",  "Error: c'è stato un problema con la ricerca.");
            response.sendError(500, "Error: " + e.getMessage());
            System.out.println("Error..." + e.getMessage());
        }
    }

    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
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
     * Serializer for a single ProductBean with cart quantity.
     */
    public static class SingleProductBeanSerializer implements JsonSerializer<ProductBean> {
        private final Cart cart;
        private final IInfoDao infoDao;

        public SingleProductBeanSerializer(Cart cart, IInfoDao infoDao) {
            this.cart = cart;
            this.infoDao = infoDao;
        }

        @Override
        public JsonElement serialize(ProductBean product, Type typeOfSrc, JsonSerializationContext context) {
            JsonObject jsonObject = new JsonObject();
            jsonObject.addProperty("codice", product.getCodice());
            jsonObject.addProperty("nome", product.getNome());
            try {
                if (infoDao != null) {
                    var info = infoDao.doRetrieveByKey(product.getCodice());
                    if (info != null) {
                        jsonObject.addProperty("costo", info.getCosto());
                    }
                }
            } catch (SQLException e) {
                // ignore
            }
            jsonObject.addProperty("cartQuantity", cart.getProductQuantity(product));
            return jsonObject;
        }
    }

    public static class ProductBeanWithCartQuantity implements JsonSerializer<Collection<ProductBean>> {
        private final Cart cart;
        private final IInfoDao infoDao;

        public ProductBeanWithCartQuantity(Cart cart, IInfoDao infoDao) {
            this.cart = cart;
            this.infoDao = infoDao;
        }

        @Override
        public JsonElement serialize(Collection<ProductBean> src, Type typeOfSrc, JsonSerializationContext context) {
            JsonArray jsonArray = new JsonArray();
            for (ProductBean product : src) {
                JsonObject jsonObject = new JsonObject();
                jsonObject.addProperty("codice", product.getCodice());
                jsonObject.addProperty("nome", product.getNome());
                try {
                    if (infoDao != null) {
                        var info = infoDao.doRetrieveByKey(product.getCodice());
                        if (info != null) {
                            jsonObject.addProperty("costo", info.getCosto());
                        }
                    }
                } catch (SQLException e) {
                    // ignore
                }
                jsonObject.addProperty("cartQuantity", cart.getProductQuantity(product));
                jsonArray.add(jsonObject);
            }
            return jsonArray;
        }
    }
}
