<%@ page contentType="text/html; charset=UTF-8"
         pageEncoding="UTF-8" errorPage="../pages/errorPage.jsp" %>

<%
    ImageDaoDataSource imageDao = new ImageDaoDataSource((DataSource) request.getServletContext().getAttribute("DataSource"));
    InfoDaoDataSource infoDao = new InfoDaoDataSource((DataSource) request.getServletContext().getAttribute("DataSource"));
    Collection<?> products = (Collection<?>) request.getAttribute("products");
    if (products == null) {
        response.sendRedirect("./${pageContext.request.contextPath}/ProductAdmin");
        return;
    }
    ProductBean product = (ProductBean) request.getAttribute("product");
%>

<!DOCTYPE html>
<html>

<%@ page contentType="text/html; charset=UTF-8"
         import="java.util.*, model.bean.ProductBean, model.bean.*, model.datasource.*, javax.sql.DataSource" %>

<head>
    <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
    <jsp:include page="../procedural/fractalNoise.jsp"/>
    <link href="${pageContext.request.contextPath}/assets/styles/base.css" rel="stylesheet" type="text/css">
    <title>Pagina prodotti</title>
</head>

<body>
<jsp:include page="../common/sticky.jsp"/>
<div class="content">
    <div class="base glassy">
        <h2> Products </h2>
        <a href="${pageContext.request.contextPath}/ProductAdmin">List</a>
        <table border="1">
            <tr>
                <th>image</th>
                <th>Code <a href="${pageContext.request.contextPath}/ProductAdmin?sort=codice"> Sort</a></th>
                <th>Name <a href="${pageContext.request.contextPath}/ProductAdmin?sort=nome"> Sort</a></th>
                <th>Description <a href="${pageContext.request.contextPath}/ProductAdmin?sort=descrizione"> Sort</a>
                </th>
                <th>Action</th>
            </tr>
            <%
                if (products != null && products.size() != 0) {
                    Iterator<?> it = products.iterator();
                    while (it.hasNext()) {
                        ProductBean bean = (ProductBean) it.next();
                        InfoBean info = infoDao.doRetrieveByKey(bean.getInfoCorrenti());
                        Collection<ImageBean> images = imageDao.doRetrieveByProduct(bean.getCodice());
                        Iterator<?> it1 = images.iterator();
                        ImageBean img = (ImageBean) it1.next();
            %>
            <tr>
                <td><img src="img/<%=img.getImg()%>" alt="product_img" width="100" height="100"></td>
                <td><%=info.getCodice()%>
                </td>
                <td><%=info.getNome()%>
                </td>
                <td><%=info.getDescrizione()%>
                </td>
                <td><a href="${pageContext.request.contextPath}/ProductAdmin?action=delete&id=<%=bean.getCodice()%>">
                    Delete</a><br>
                    <a href="${pageContext.request.contextPath}/ProductAdmin?action=read&id=<%=bean.getCodice()%>">
                        Details</a><br>
                    <a href="${pageContext.request.contextPath}/ProductAdmin?action=addC&id=<%=bean.getCodice()%>"> Add
                        to cart</a><br>
                </td>
            </tr>
            <%
                }
            } else {
            %>
            <tr>
                <td colspan="6"> No products available</td>
            </tr>
            <%
                }
            %>
        </table>

        <h2>Dettagli</h2>
        <%
            if (product != null) {
                Collection<ImageBean> images = imageDao.doRetrieveByProduct(product.getCodice());
                Iterator<?> it1 = images.iterator();
                InfoBean info = infoDao.doRetrieveByKey(product.getInfoCorrenti());
        %>
        <div class="base glassy">
            <table border="1">
                <tr>
                    <th>Image</th>
                    <th>Code</th>
                    <th>Name</th>
                    <th>Description</th>
                    <th>Price</th>
                    <th>Quantity</th>

                </tr>
                <tr>
                    <td>
                        <% while (it1.hasNext()) {
                            ImageBean img = (ImageBean) it1.next(); %>
                        <img src="img/<%=img.getImg()%>" alt="product_img" width="300" height="300">
                        <% } %></td>
                    <td><%=product.getCodice()%>
                    </td>
                    <td><%=info.getNome()%>
                    </td>
                    <td><%=info.getDescrizione()%>
                    </td>
                    <td><%=info.getCosto()%>
                    </td>
                    <td><%=info.getDisponibilità()%>
                    </td>
                </tr>
            </table>
        </div>
        <%
            }
        %>
        <div class="base glassy">
            <h2>Insert</h2>
            <form action="ProductUpload" method="post" enctype="multipart/form-data">
                <input type="hidden" name="action" value="insert">

                <label for="name">Name:</label><br>
                <input name="name" type="text" maxlength="20" required placeholder="enter name"><br>

                <label for="myfile">image:</label><br>
                <input name="myfile" type="file" required accept="image/*"><br>

                <label for="type">type:</label><br>
                <input name="type" type="text" maxlength="20" required placeholder="enter type"><br>

                <label for="description">Description:</label><br>
                <textarea name="description" maxlength="100" rows="3" required
                          placeholder="enter description"></textarea><br>

                <label for="price">Price:</label><br>
                <input name="price" type="number" step="0.01" min="0.00" value="0.0" required><br>

                <label for="quantity">Quantity:</label><br>
                <input name="quantity" type="number" min="1" value="1" required><br>

                <input type="submit" value="Add"><input type="reset" value="Reset">
            </form>
        </div>
    </div>
</div>
    <jsp:include page="../common/footer.jsp"/>
</body>
</html>