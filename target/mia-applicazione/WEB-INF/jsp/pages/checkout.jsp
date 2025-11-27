<%@ page contentType="text/html; charset=UTF-8"
         pageEncoding="UTF-8" errorPage="errorPage.jsp" %>
<%
    InfoDaoDataSource infoDao = new InfoDaoDataSource((DataSource) request.getServletContext().getAttribute("DataSource"));
    AddressDaoDataSource addressDao = new AddressDaoDataSource((DataSource) request.getServletContext().getAttribute("DataSource"));
    Collection<?> addresses = (Collection<?>) request.getAttribute("addresses");
    UserBean user;
    user = (UserBean) request.getSession().getAttribute("LoggedUser");
    if (addresses == null) {
        if (user == null) {
            request.getSession().setAttribute("Checkout", "SI");
            response.sendRedirect(request.getContextPath() + "/loginView.jsp");
        } else response.sendRedirect("./checkoutcontrol");
        return;
    }
    Collection<?> items = (Collection<?>) request.getAttribute("containList");
    OrderBean order = (OrderBean) request.getAttribute("order");
%>

<!DOCTYPE html>
<html>

<%@ page contentType="text/html; charset=UTF-8"
         import="java.util.*, model.bean.*, model.datasource.*, javax.sql.DataSource" %>
<%@ page import="model.bean.OrderBean" %>

<head>
    <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
    <jsp:include page="../procedural/fractalNoise.jsp"/>
    <link href="${pageContext.request.contextPath}/assets/styles/base.css" rel="stylesheet" type="text/css">
    <link href="${pageContext.request.contextPath}/assets/styles/pages/checkout.css" rel="stylesheet" type="text/css">
    <title>Checkout</title>
</head>

<body>
<jsp:include page="../common/sticky.jsp"/>
<div class="content">
    <div class="base glassy">
        <h1>Checkout </h1>
        
        <% if (order.getStato() == "completato") {%>
        <h2>Acquisto completato!</h2>
        <% } else if (items.isEmpty()) {%>
        <h2>Il tuo carello è vuoto!</h2>
        <%} else {%>

        <h2>Scegli l'indirizzo di spedizione</h2>
        <form action="${pageContext.request.contextPath}/Checkout" id="addressForm" method="post">

            <label for="address">Scegli l'indirizzo di spedizione</label>
            <select name="address" id="address">
                <%
                    Iterator<?> it1 = addresses.iterator();
                    while (it1.hasNext()) {
                        AddressBean bean = (AddressBean) it1.next();
                %>
                <option value="<%=bean.getId()%>"><%=bean.selectString()%>
                </option>
                <%} %>
            </select> <br>
            <input type="submit" value="scegli"><input type="reset" value="Reset">
        </form>

        <h2>Il tuo ordine </h2>
        <a href="checkoutcontrol">List</a>
        <table border="1">
            <tr>
                <th>Code</th>
                <th>Data</th>
                <th>Stato</th>
                <th>Saldo</th>
                <th>Indirizzo di spedizione</th>
            </tr>
            <tr>
                <td><%=order.getCodice()%>
                </td>
                <td><%=order.getDataOrdine()%>
                </td>
                <td><%=order.getStato()%>
                </td>
                <td><%=order.getSaldoTotale()%>
                </td>
                <%if (order.getIndirizzo() == " ") {%>
                <td>Non selezionato</td>
                <%
                } else {
                    String a = order.getIndirizzo();
                    System.out.println(a);
                    AddressBean ad = addressDao.doRetrieveByKey(a, user.getUsername());
                    System.out.println(ad.getUtente());
                %>
                <td><%=ad.selectString()%>
                </td>
                <%} %>
            </tr>
        </table>


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

        <form action="${pageContext.request.contextPath}/Checkout" id="confirmForm" method="post">
            <input type="hidden" name="action" id="action" value="confirm">
            <input type="hidden" name="address" id="address" value="<%=request.getParameter("address")%>">
            <input type="submit" value="conferma">
        </form>
        <% } %>
    </div>
</div>
<jsp:include page="../common/footer.jsp"/>
</body>

</html>