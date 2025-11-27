<%--
  Created by IntelliJ IDEA.
  User: luigi
  Date: 15/07/2024
  Time: 16:20
  To change this template use File | Settings | File Templates.
--%>
<%@ page language="java" contentType="text/html; charset=UTF-8"
         pageEncoding="UTF-8" errorPage="../pages/errorPage.jsp" %>

<%
    Collection<?> orders = (Collection<?>) request.getAttribute("orders");
    if (orders == null) {
        response.sendRedirect("./user/orders");
        return;
    }
    Collection<?> items = (Collection<?>) request.getAttribute("Details");
    InfoDaoDataSource infoDao = new InfoDaoDataSource((DataSource) request.getServletContext().getAttribute("DataSource"));
    UserDaoDataSource userDao = new UserDaoDataSource((DataSource) request.getServletContext().getAttribute("DataSource"));
%>

<!DOCTYPE html>
<html>

<%@ page contentType="text/html; charset=UTF-8"
         import="java.util.*, model.bean.ProductBean, model.bean.*, model.Cart.*, model.datasource.*, javax.sql.DataSource" %>

<head>
    <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
    <jsp:include page="../procedural/fractalNoise.jsp"/>
    <link href="${pageContext.request.contextPath}/assets/styles/base.css" rel="stylesheet" type="text/css">
    <script type="text/javascript" src="${pageContext.request.contextPath}/assets/script/pages/orders.js"></script>
    <title>Order History</title>
</head>

<body>
<jsp:include page="../common/sticky.jsp"/>
<div class="content">
    <div class="base glassy">
        <h2> Ordini </h2>
        <a href="product">List</a>
        <table border="1">
            <tr>
                <th>User</th>
                <th>Code</th>
                <th>Status</th>
                <th>Data</th>
                <th>Balance</th>
                <th>Action</th>
            </tr>
            <%
                if (orders != null && orders.size() != 0) {
                    Iterator<?> it = orders.iterator();
                    while (it.hasNext()) {
                        OrderBean bean = (OrderBean) it.next();
            %>
            <tr>
                <td><%=bean.getUtente()%>
                </td>
                <td><%=bean.getCodice()%>
                </td>
                <td><%=bean.getDataOrdine()%>
                </td>
                <td><%=bean.getStato()%>
                </td>
                <td><%=bean.getSaldoTotale()%>
                </td>
                <td>
                    <a href="${pageContext.request.contextPath}/admin/orders?action=orderDetails&orderUser=<%=bean.getUtente()%>&orderNum=<%=bean.getCodice()%>">
                        Details</a><br>
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
    </div>
    <div class="base glassy">
        <h2>Details</h2>
        <table border="1">
            <tr>
                <th>Name</th>
                <th>Description</th>
                <th>Price</th>
                <th>Quantity</th>

            </tr>

            <%
                if (items != null && items.size() != 0) {
                    Iterator<?> it = items.iterator();
                    while (it.hasNext()) {
                        ContainBean bean = (ContainBean) it.next();
                        InfoBean info = infoDao.doRetrieveByKey(bean.getCodiceProdotto());

            %>

            <tr>
                <td><%=info.getNome()%>
                </td>
                <td><%=info.getDescrizione()%>
                </td>
                <td><%=info.getCosto()%>
                </td>
                <td><%=bean.getQuantità()%>
                </td>
            </tr>
            <%
                    }
                }
            %>
        </table>
        <h2>Filter </h2>
        <form action="${pageContext.request.contextPath}/admin/orders" id="filterForm" method="get">
            <input type="hidden" name="action" id="action" value="insert">

            <label for="user">user:</label>
            <select name="user" id="user">
                <option value="">all</option>
                <%
                    Collection<?> users = (Collection<?>) userDao.doRetrieveAll("");
                    Iterator<?> it = users.iterator();
                    while (it.hasNext()) {
                        UserBean bean = (UserBean) it.next();
                %>
                <option value="<%=bean.getUsername()%>"><%=bean.getUsername()%>
                </option>
                <%} %>

            </select> <br>

            <label for="dateMin">Min Date:</label>
            <input name="dateMin" id="dateMin" type="date" placeholder="yyyy-mm-dd"><br>

            <label for="dateMax">Max Date:</label>
            <input name="dateMax" id="dateMax" type="date" placeholder="yyyy-mm-dd"><br>

            <input type="submit" value="Add"><input type="reset" value="Reset">
        </form>
    </div>
</div>
<jsp:include page="../common/footer.jsp"/>
</body>
</html>
