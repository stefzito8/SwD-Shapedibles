 <%@ page language="java" contentType="text/html; charset=UTF-8"
    pageEncoding="UTF-8" errorPage="WEB-INF/jsp/pages/errorPage.jsp"%>

<% 
	ImageDaoDataSource imageDao = new ImageDaoDataSource( (DataSource) request.getServletContext().getAttribute("DataSource"));
    InfoDaoDataSource infoDao = new InfoDaoDataSource( (DataSource) request.getServletContext().getAttribute("DataSource"));
	Collection<?> products = (Collection<?>) request.getAttribute("products");
	if(products == null) {
		response.sendRedirect("./product");
		return;
	}
	ProductBean product = (ProductBean) request.getAttribute("product");
%>

<!DOCTYPE html>
<html>

<%@ page contentType="text/html; charset=UTF-8" import="java.util.*, model.bean.ProductBean, model.bean.*, model.Cart.*, model.datasource.*, javax.sql.DataSource"%>

<head>
	<meta http-equiv="Content-Type" content="text/html; charset=UTF-8">
	<link rel="preconnect" href="https://fonts.googleapis.com">
	<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
	<link href="https://fonts.googleapis.com/css2?family=Merriweather+Sans&display=swap" rel="stylesheet">
	<link href="assets/styles/pages/product.css" rel="stylesheet" type="text/css">
	<title>Pagina prodotti</title>
</head>

<body>
	<div class="productContainer">

  <h2> Products </h2>
  <a href="product">List</a>
  <table border="1">
   <tr>
   		<th>image</th>
   		<th>Code <a href="product?sort=codice"> Sort</a></th>
   		<th>Name <a href="product?sort=nome"> Sort</a></th>
   		<th>Description <a href="product?sort=descrizione"> Sort</a></th>
   		<th>Action</th>
   </tr>
  <%
	if(products != null && products.size()!= 0) {
		Iterator<?> it = products.iterator();
		while (it.hasNext()) {
			ProductBean bean = (ProductBean) it.next();
			InfoBean info = infoDao.doRetrieveByKey(bean.getInfoCorrenti());
			Collection<ImageBean> images = imageDao.doRetrieveByProduct(bean.getCodice());
			Iterator<?> it1 = images.iterator();
			ImageBean img = (ImageBean) it1.next();
  %>
  <tr>
  		<td><img src="img/<%=img.getImg()%>" alt="product_img" width="100" height="100"></td>	
   		<td><%=info.getCodice()%></td>
   		<td><%=info.getNome()%></td>
   		<td><%=info.getDescrizione()%></td>
   		<td>
   			 <a href="product?action=read&id=<%=bean.getCodice()%>"> Details</a><br>
   			 <a href="product?action=addC&id=<%=bean.getCodice()%>"> Add to cart</a><br>
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
  <% 
  	if (product != null) {
  		Collection<ImageBean> images = imageDao.doRetrieveByProduct(product.getCodice());
		Iterator<?> it1 = images.iterator();
  		InfoBean info = infoDao.doRetrieveByKey(product.getInfoCorrenti());
  %>
  <table border="1">
  	<tr>
  	    <th>Image</th>  
  		<th>Code</th>
  		<th>Name</th>
  		<th>Description</th>
  		<th>Price</th>
  		<th>Quantity</th>  
  		
  	</tr>
  	<tr>
  		<td>
  	    <% while (it1.hasNext()) { 
  	    ImageBean img = (ImageBean) it1.next(); %>
  		<img src="img/<%=img.getImg()%>" alt="product_img" width="300" height="300">
  		<% } %>  </td>
  		<td><%=product.getCodice()%></td>
   		<td><%=info.getNome()%></td>
   		<td><%=info.getDescrizione()%></td>
   		<td><%=info.getCosto()%></td>
   		<td><%=info.getDisponibilità()%></td>
  	</tr>
  </table>
  <%
  	}
  %>
  
  <a href="WEB-INF/jsp/pages/loginView.jsp" > Login </a>
  <a href="WEB-INF/jsp/pages/RegisterView.jsp" > Register </a>
	<a href="WEB-INF/jsp/pages/Cart.jsp" > Cart </a>
   <a href="WEB-INF/jsp/pages/Checkout.jsp" > Checkout </a>
	<a href="WEB-INF/jsp/admin/ProductAdmin.jsp" > Admin </a>
	<a href="WEB-INF/jsp/pages/OrderHistory.jsp" > Order History </a>
	</div>
</body>
</html>