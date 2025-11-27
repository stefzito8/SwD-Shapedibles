<%@ page language="java" contentType="text/html; charset=UTF-8"
         pageEncoding="UTF-8" errorPage="./errorPage.jsp" %>

<%
    ImageDaoDataSource imageDao = new ImageDaoDataSource((DataSource) request.getServletContext().getAttribute("DataSource"));
    InfoDaoDataSource infoDao = new InfoDaoDataSource((DataSource) request.getServletContext().getAttribute("DataSource"));
    ProductBean product = (ProductBean) request.getAttribute("productE");
    InfoBean info = (InfoBean) request.getAttribute("infoE");
    NutritionTableBean nut = (NutritionTableBean) request.getAttribute("nutritionTableE");
    if (product == null) {
        response.sendRedirect("./productedit");
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
    <title>edit <%=product.getNome()%>
    </title>
</head>

<body>
<jsp:include page="../common/sticky.jsp"/>
<div class="content">
    <div class="base glassy">
        <h2>edit</h2>
        <form action="${pageContext.request.contextPath}/ProductEdit" method="post" enctype="multipart/form-data">
            <!---->
            <input type="hidden" name="action" value="edit">
            <input type="hidden" name="product" value="<%=product.getCodice()%>">

            <label for="name">Name:</label><br>
            <input name="name" type="text" maxlength="20" value="<%=info.getNome()%>"><br>

            <label for="type">type:</label><br>
            <input name="type" type="text" maxlength="20" value="<%=info.getTipologia()%>"><br>

            <label for="description">Description:</label><br>
            <textarea name="description" maxlength="1000" rows="8"><%=info.getDescrizione()%></textarea><br>

            <label for="price">Price:</label><br>
            <input name="price" type="number" step="0.01" min="0.00" value="<%=info.getCosto()%>"><br>

            <label for="quantity">Quantity:</label><br>
            <input name="quantity" type="number" min="1" value="<%=info.getDisponibilità()%>"><br>

            <%if (!info.getTipologia().contains("altro")) {%>
            <h2> Valori nutrizionali</h2>

            <label for="cal">Energia:</label><br>
            <input name="cal" type="number" min="1" value="<%=nut.getEnergia()%>"><br>

            <label for="fats">Grassi:</label><br>
            <input name="fats" type="number" step="0.01" min="0.00" value="<%=nut.getGrassi()%>"><br>

            <label for="satFats">Grassi saturi:</label><br>
            <input name="satFats" type="number" step="0.01" min="0.00" value="<%=nut.getGrassiSaturi()%>"><br>

            <label for="carbs">Carboedrati:</label><br>
            <input name="carbs" type="number" step="0.01" min="0.00" value="<%=nut.getCarboedrati()%>"><br>

            <label for="sugars">Zuccheri:</label><br>
            <input name="sugars" type="number" step="0.01" min="0.00" value="<%=nut.getZucherri()%>"><br>

            <label for="fibers">Fibre:</label><br>
            <input name="fibers" type="number" step="0.01" min="0.00" value="<%=nut.getFibre()%>"><br>

            <label for="protein">Proteine:</label><br>
            <input name="protein" type="number" step="0.01" min="0.00" value="<%=nut.getProteine()%>"><br>

            <label for="salt">Sale:</label><br>
            <input name="salt" type="number" step="0.01" min="0.00" value="<%=nut.getSale()%>"><br>
            <%} %>
            <h2>Imagini</h2>

            <label for="squareFile">square image:</label><br>
            <input name="squareFile" type="file" accept="image/*"><br>

            <label for="TransFile">Transparent image:</label><br>
            <input name="TransFile" type="file" accept="image/*"><br> -->

            <label for="wideFile">wide image:</label><br>
            <input name="wideFile" type="file" accept="image/*"><br> -->

            <input type="submit" value="Apply Edits"><input type="reset" value="Reset">
        </form>
    </div>
</div>
<jsp:include page="../common/footer.jsp"/>
</body>
</html>