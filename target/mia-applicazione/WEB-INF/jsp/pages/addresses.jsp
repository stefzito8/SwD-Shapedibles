<%@ page language="java" contentType="text/html; charset=UTF-8"
         pageEncoding="ISO-8859-1" errorPage="errorPage.jsp" %>
<%
    Collection<?> addresses = (Collection<?>) request.getAttribute("addresses");
    if (addresses == null) {
        response.sendRedirect("./addresses");
        return;
    }
%>

<!DOCTYPE html>
<html>

<%@ page contentType="text/html; charset=UTF-8"
         import="java.util.*, model.bean.ProductBean, model.bean.*, model.Cart.*, model.datasource.*, javax.sql.DataSource" %>

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
        <h2> Your addresses: </h2>
        <table border="1">
            <%
                if (addresses != null && addresses.size() != 0) {
                    Iterator<?> it = addresses.iterator();
                    while (it.hasNext()) {
                        AddressBean bean = (AddressBean) it.next();
            %>
            <tr>
                <td><%=bean.selectString()%>
                </td>
                <td><a href="addresses?action=delete&id=<%=bean.getId()%>"> Delete</a>
                </td>
            </tr>
            <%
                }
            } else {
            %>
            <tr>
                <td colspan="6"> No Addresses available</td>
            </tr>
            <%
                }
            %>
        </table>
    </div>
    <div class="base glassy">
        <h2>Insert</h2>
        <form action="addresses" method="post" id="insertForm">
            <input type="hidden" name="action" value="Add">

            <label for="paese">Nation:</label><br>
            <input name="paese" type="text" maxlength="50" required placeholder="enter your nation"><br>

            <label for="citta">City:</label><br>
            <input name="citta" type="text" maxlength="50" required placeholder="enter your city"><br>

            <label for="strada">Street:</label><br>
            <input name="strada" type="text" maxlength="100" required placeholder="enter your street"><br>


            <label for="numero">Street Number:</label><br>
            <input name="numero" type="number" min="0" value="0" required><br>

            <label for="cap">CAP:</label><br>
            <input name="cap" type="text" maxlength="6" required placeholder="enter your CAP"><br>


            <input type="submit" value="Add"><input type="reset" value="Reset">
        </form>
    </div>
</div>
<jsp:include page="../common/footer.jsp"/>
</body>
</html>