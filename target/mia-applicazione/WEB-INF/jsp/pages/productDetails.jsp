<%--@elvariable id="productQuantity" type="int"--%>
<%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8" errorPage="./errorPage.jsp"%>

<%
	Cart cart = (Cart) request.getSession().getAttribute("cart");
	if(cart == null)
	{
		cart = new Cart();
		request.getSession().setAttribute("cart", cart);
	}
    ProductBean product = (ProductBean) request.getAttribute("product");
	InfoBean info = (InfoBean) request.getAttribute("info");
    Collection<?> images = (Collection<?>) product.getImages();
	Iterator<?> it = images.iterator();
	String squareImage = request.getContextPath() + "/assets/images/products/" + "fallback_square.jpg";
	String wideImage = request.getContextPath() + "/assets/images/products/" + "fallback_wide.jpg";
	while (it.hasNext()) {
		ImageBean img = (ImageBean) it.next();
		if (img.getImgIfString("square") != null) {
			squareImage = request.getContextPath() + "/assets/images/products/" + img.getImg();
		}
		if (img.getImgIfString("wide") != null) {
			wideImage = request.getContextPath() + "/assets/images/products/" + img.getImg();
		}
	}

	NutritionTableBean nut = (NutritionTableBean) request.getAttribute("nutritionTable");
%>

<!DOCTYPE html>
<html>

<%@ page contentType="text/html; charset=UTF-8" import="java.util.*, model.bean.ProductBean, model.bean.*, model.Cart.*, model.datasource.*, javax.sql.DataSource"%>
<%@ page import="model.Cart" %>

<head>
	<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
	<jsp:include page="../procedural/fractalNoise.jsp"/>
	<title><%=product.getNome()%></title>
	<link href="${pageContext.request.contextPath}/assets/styles/base.css" rel="stylesheet" type="text/css">
	<link href="${pageContext.request.contextPath}/assets/styles/pages/productDetails.css" rel="stylesheet" type="text/css">
	<script>
		var productId = <%=product.getCodice()%>;
	</script>
	<script src="${pageContext.request.contextPath}/assets/script/pages/productDetails.js"></script>
</head>
<body>
	<jsp:include page="../common/sticky.jsp"/>
	<div class="content">
		
		<div class="glassy product-details">
			<h2><%=product.getNome()%></h2>
			<div class="details">
				<div class="general">
					<img id="squareImage"  src="<%=squareImage%>" alt="<%=product.getNome()%>">
					<div class="info">
						<div>
							<span class="material-symbols-rounded">description</span>
							<span><%=info.getDescrizione()%></span>
						</div>
						<div>
							<span class="material-symbols-rounded">euro</span>
							<span><%=info.getCosto()%></span>
						</div>
						<div>
							<span class="material-symbols-rounded">sell</span>
							<span><%=info.getTipologia()%></span>
						</div>
						<div>
							<span class="material-symbols-rounded">production_quantity_limits</span>
							<span><%=info.getDisponibilità()%></span>
						</div>

					</div>
				</div>
			</div>
<%--			<div class="buttons">--%>
<%--				<div class="cart-interaction">--%>
<%--					<button id="productCartPlus">+</button>--%>
<%--					<div id="productCartQuantity"><%cart.getProductQuantity(product);%></div>--%>
<%--					<button id="productCartMinus">-</button>--%>
<%--				</div>--%>
<%--			</div>--%>
			<div class="carving">
				<img id="wideImage"  src="<%=wideImage%>" alt="<%=product.getNome()%>">
			</div>
		</div>
		<% if (!info.getTipologia().equals("Shaker")) {%>
			<div class="base glassy" id="nutritionBase">
				<table border="1">
					<tr>
						<th>Valore Nutrizionale</th>
						<th>Quantità</th>
					</tr>
					<tr>
						<td>energia</td>
						<td><%=nut.getEnergia()%> kl</td>
					</tr>
					<tr>
						<td>grassi</td>
						<td><%=nut.getGrassi()%> g</td>
					</tr>
					<tr>
						<td>di cui saturi</td>
						<td><%=nut.getGrassiSaturi()%> g</td>
					</tr>
					<tr>
						<td>carboidrati</td>
						<td><%=nut.getCarboedrati()%> g</td>
					</tr>
					<tr>
						<td>zuccheri</td>
						<td><%=nut.getZucherri()%> g</td>
					</tr>
					<tr>
						<td>fibre</td>
						<td><%=nut.getFibre()%> g</td>
					</tr>
					<tr>
						<td>proteine</td>
						<td><%=nut.getProteine()%> g</td>
					</tr>
					<tr>
						<td>sale</td>
						<td><%=nut.getSale()%> g</td>
					</tr>
	
				</table>
			</div>
		<% } %>
	</div>
	<jsp:include page="../common/footer.jsp"/>
</body>
</html>