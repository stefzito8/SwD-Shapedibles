<%@ page import="model.bean.ImageBean" %>
<%@ page import="model.bean.ProductBean" %>
<%@ page import="model.Utils" %>
<%@ page import="java.util.*" %>
<%
    Collection<?> products = (Collection<?>) request.getAttribute("products");
    Object[] productsArray = products.toArray();
    Random random = new Random();


    ProductBean shakerOne = (ProductBean) products.toArray()[2];
    ProductBean shakerTwo = (ProductBean) products.toArray()[17];
%>
<%@ page contentType="text/html;charset=UTF-8" %>
<html>
<head>
    <title>Shapedibles</title>
    
    <jsp:include page="../procedural/fractalNoise.jsp"/>
    
    <link rel="stylesheet" href="${pageContext.request.contextPath}/assets/styles/base.css">
    <link href="${pageContext.request.contextPath}/assets/styles/pages/home.css" rel="stylesheet" type="text/css">
</head>
<body>
    <jsp:include page="../common/sticky.jsp"/>
    <div class="content">
        <div class="shaker-carousel glassy">
            <a href="${pageContext.request.contextPath}<%="/ProductDetails?product=" + shakerOne.getCodice()%>">
                <img src="<%= Utils.getSquareImage(request,shakerOne,"transparent") %>" alt="Shaker Carousel 1">
            </a>
            <a href="${pageContext.request.contextPath}<%="/ProductDetails?product=" + shakerTwo.getCodice()%>">
                <img src="<%= Utils.getSquareImage(request,shakerTwo,"transparent") %>" alt="Shaker Carousel 2">
            </a>
        </div>
        <div class="product-carousel">
            <h2>Prodotti in vetrina</h2>
            <div class="products">
            <%
                for (int i = productsArray.length - 1; i > 0; i--) {
                    int index = random.nextInt(i + 1);
                    // Swap
                    Object temp = productsArray[index];
                    productsArray[index] = productsArray[i];
                    productsArray[i] = temp;
            %>
            <div class="product-carousel-container glassy">
                <div class="info">
                    <span id="name"><%=((ProductBean) productsArray[i]).getNome()%></span>
                </div>
                <a href="${pageContext.request.contextPath}/ProductDetails?product=<%=((ProductBean) productsArray[i]).getCodice()%>">
                    <img src="<%= Utils.getSquareImage(request,(ProductBean) productsArray[i],"square") %>" alt="Product Carousel <%=i%>">
                </a>
            </div>
            <%}%>
            </div>
        </div>
    </div>
    <jsp:include page="../common/footer.jsp"/>
</body>
</html>