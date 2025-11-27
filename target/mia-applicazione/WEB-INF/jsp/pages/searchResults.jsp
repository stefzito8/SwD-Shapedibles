<%@ page contentType="text/html;charset=UTF-8"%>
<%@ taglib uri="http://java.sun.com/jsp/jstl/core" prefix="c" %>
<html>
<head>
    <title>Search Results</title>
</head>
<body>
<h2>Search Results</h2>
<jsp:useBean id="searchResults" scope="request" type="java.util.List"/>
<c:if test="${not empty searchResults}">
    <ul>
        <c:forEach var="product" items="${searchResults}">
            <li>
                <strong>Name:</strong> ${product.nome} <br/>
                <strong>Cost:</strong> ${product.costo} <br/>
                <strong>Description:</strong> ${product.descrizione} <br/>
                <strong>Availability:</strong> ${product.disponibilità} <br/>
                <strong>Type:</strong> ${product.tipologia}
            </li>
        </c:forEach>
    </ul>
</c:if>
<c:if test="${empty searchResults}">
    <p>No products found.</p>
</c:if>
</body>
</html>