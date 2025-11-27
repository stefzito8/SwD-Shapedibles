<%--
  Created by IntelliJ IDEA.
  User: luigi
  Date: 17/07/2024
  Time: 16:03
  To change this template use File | Settings | File Templates.
--%>
<%@ page language="java" contentType="text/html; charset=UTF-8"
         pageEncoding="UTF-8" errorPage="../pages/errorPage.jsp" %>

<%
    Collection<?> users = (Collection<?>) request.getAttribute("users");
    if (users == null) {
        response.sendRedirect("./users");
        return;
    }

    UserBean loggedUser = (UserBean) session.getAttribute("LoggedUser");
    String loggedUsername = loggedUser != null ? loggedUser.getUsername() : "";
%>

<!DOCTYPE html>
<html>

<%@ page contentType="text/html; charset=UTF-8"
         import="java.util.*, model.bean.ProductBean, model.bean.*, model.Cart.*, model.datasource.*, javax.sql.DataSource" %>

<head>
    <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
    <jsp:include page="../procedural/fractalNoise.jsp"/>
    <link href="${pageContext.request.contextPath}/assets/styles/base.css" rel="stylesheet" type="text/css">
    <title>Gestione Account</title>
</head>

<body>
<jsp:include page="../common/sticky.jsp"/>
<div class="content">
    <div class="base glassy">
        <div class="productContainer">
            <h2> Account </h2>
            <a href="product">List</a>
            <table border="1">
                <tr>
                    <th>Username</th>
                    <th>Email</th>
                    <th>Sesso</th>
                    <th>Nome e Cognome</th>
                    <th>Data di nascita</th>
                    <th>Paese</th>
                    <th>Admin</th>
                </tr>
                <%
                    if (users != null && users.size() != 0) {
                        Iterator<?> it = users.iterator();
                        while (it.hasNext()) {
                            UserBean bean = (UserBean) it.next();
                %>
                <tr>
                    <td><%=bean.getUsername()%>
                    </td>
                    <td><%=bean.getEmail()%>
                    </td>
                    <td><%=bean.getSesso()%>
                    </td>
                    <td><%=bean.getNomeCognome()%>
                    </td>
                    <td><%=bean.getDataNascita()%>
                    </td>
                    <td><%=bean.getPaese()%>
                    </td>
                    <td><%=bean.getUserAdmin()%>
                    </td>
                    <td>
                        <a href="users?action=admin&username=<%=bean.getUsername()%>">Make Admin</a><br>
                        <% if (!bean.getUsername().equals(loggedUsername)) { %>
                        <a href="users?action=delete&username=<%=bean.getUsername()%>">Delete user</a><br>
                        <% } %>
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
    </div>
</div>
<jsp:include page="../common/footer.jsp"/>
</body>
</html>
