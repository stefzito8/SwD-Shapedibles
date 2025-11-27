<%--
  Created by IntelliJ IDEA.
  User: luigi
  Date: 17/07/2024
  Time: 16:31
  To change this template use File | Settings | File Templates.
--%>
<%@ page language="java" contentType="text/html; charset=UTF-8"
         pageEncoding="UTF-8" errorPage="errorPage.jsp" %>

<%
    UserBean user = (UserBean) request.getSession().getAttribute("LoggedUser");
    Collection<?> userOrders = (Collection<?>) request.getAttribute("OrdersLoggedUser");
    if (userOrders == null) {
        response.sendRedirect("./user/profile");
        return;
    }
    Collection<?> items = (Collection<?>) request.getAttribute("Details");
    InfoDaoDataSource infoDao = new InfoDaoDataSource((DataSource) request.getServletContext().getAttribute("DataSource"));
%>

<!DOCTYPE html>
<html>

<%@ page contentType="text/html; charset=UTF-8"
         import="java.util.*, model.bean.ProductBean, model.bean.*, model.Cart.*, model.datasource.*, javax.sql.DataSource" %>

<head>
    <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
    <link href="${pageContext.request.contextPath}/assets/styles/base.css" rel="stylesheet" type="text/css">
    <link href="${pageContext.request.contextPath}/assets/styles/pages/userProfile.css" rel="stylesheet"
          type="text/css">
    <title>User Profile</title>
</head>

<body>
<jsp:include page="../common/sticky.jsp"/>
<div class="content">
    <div class="base glassy">
        <h1> Profilo Utente </h1>
        <p><strong>Username: </strong></p><span> <%=user.getUsername()%> </span>
        <p><strong>Email: </strong></p><span> <%=user.getEmail()%> </span>
        <p><strong>Nome e Cognome: </strong></p><span> <%=user.getNomeCognome()%> </span>
        <p><strong>Data di Nascita: </strong></p><span> <%=user.getDataNascita()%> </span>
        <p><strong>Paese: </strong></p><span> <%=user.getPaese()%> </span>
        <p><strong>Sesso: </strong></p><span> <%=user.getSesso()%> </span>
        <h2> I tuoi ordini </h2>
        <a href="product">List</a>
        <table border="1">
            <tr>
                <th>Utente</th>
                <th>Codice</th>
                <th>Stato</th>
                <th>Data</th>
                <th>Saldo</th>
                <th>Azione</th>
            </tr>
            <%
                if (userOrders != null && userOrders.size() != 0) {
                    Iterator<?> it = userOrders.iterator();
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
                    <a href="${pageContext.request.contextPath}/UserProfile?action=orderDetails&orderUser=<%=bean.getUtente()%>&orderNum=<%=bean.getCodice()%>">
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
        <h2>Dettagli</h2>
        <table border="1">
            <tr>
                <th>Nome</th>
                <th>Descrizione</th>
                <th>Prezzo</th>
                <th>Quantità</th>

            </tr>
            <%
                if (items != null && !items.isEmpty()) {
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
    </div>
</div>
<jsp:include page="../common/footer.jsp"/>
</body>
</html>