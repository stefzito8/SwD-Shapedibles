<%@ page language="java" contentType="text/html; charset=UTF-8"
         pageEncoding="UTF-8" isErrorPage="true" %>
<!DOCTYPE html>
<html>

<%@ page contentType="text/html; charset=UTF-8" import="java.util.*" %>


<head>
    <meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
    <jsp:include page="../procedural/fractalNoise.jsp"/>
    <link href="${pageContext.request.contextPath}/assets/styles/base.css" rel="stylesheet" type="text/css">
    <link href="${pageContext.request.contextPath}/assets/styles/pages/error.css" rel="stylesheet" type="text/css">
    <title>Pagina di errore</title>
</head>

<body>
<jsp:include page="../common/sticky.jsp"/>
<div class="content">
    <h1> C'è stato un errore!</h1>
    <%
        String error = (String) request.getAttribute("error");
        if (error == null || error.isEmpty()) {
    %>
    <a href="${pageContext.request.contextPath}"  class="hyperlink"> Prego riprovare più tardi</a>
    <% } else { %>
    <h1><%=error%>
    </h1> <br>
    <a href="${pageContext.request.contextPath}" class="hyperlink"> Prego riprovare più tardi</a>
    <% } %>
</div>
<jsp:include page="../common/footer.jsp"/>
</body>
</html>