<%@ page contentType="text/html; charset=UTF-8"
         pageEncoding="UTF-8" errorPage="errorPage.jsp" %>

<%
    Cart cart = (Cart) session.getAttribute("cart");
    System.out.println(cart);
%>

<!DOCTYPE html>
<html>

<%@ page contentType="text/html; charset=UTF-8"
         import="java.util.*, model.bean.*, model.Cart, javax.sql.DataSource, model.datasource.*" %>
<%@ page import="java.sql.SQLException" %>

<head>
    <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
    <jsp:include page="../procedural/fractalNoise.jsp"/>
    <link href="${pageContext.request.contextPath}/assets/styles/base.css" rel="stylesheet" type="text/css">
    <link href="${pageContext.request.contextPath}/assets/styles/pages/cart.css" rel="stylesheet" type="text/css">
    <title>Carrello</title>
</head>

<body>
<jsp:include page="../common/sticky.jsp"/>
<div class="content">
    <div class="base glassy">
        <h2>Carrello</h2>
        <%
            InfoDaoDataSource DAOEmily = new InfoDaoDataSource((DataSource) request.getServletContext().getAttribute("DataSource"));
            if (!cart.getProducts().isEmpty()) {
        %>
        <table border="1">
            <tr>
                <th>Nome</th>
                <th>Prezzo</th>
                <th>Quantità</th>
                <th>Azioni</th>
            </tr>
            <% List<ProductBean> prodcart = (List<ProductBean>) cart.getProducts();
                for (ProductBean beancart : prodcart) {
                    InfoBean infob = null;
                    try {
                        infob = DAOEmily.doRetrieveByKey(beancart.getCodice());
                    } catch (SQLException e) {
                        throw new RuntimeException(e);
                    }
            %>
            <tr>
                <td><%=infob.getNome()%>
                </td>
                <td><%=infob.getCosto()%>
                </td>
                <td><%=cart.getProductQuantity(beancart)%>
                </td>
                <td><a class="hyperlink" href="Cart?action=deleteC&id=<%=beancart.getCodice()%>">Delete from cart</a></td>
            </tr>
            <%} %>
        </table>
        <a class="primary-round-btn nodeco checkout" href="${pageContext.request.contextPath}/user/checkout">
            <span class="material-symbols-rounded">check</span>
        </a>
        <% } else { %>
            <p id="empty">Oops, sembra non ci sia nulla...</p>
        <% } %>
    </div>
</div>
<jsp:include page="../common/footer.jsp"/>
</body>
</html>