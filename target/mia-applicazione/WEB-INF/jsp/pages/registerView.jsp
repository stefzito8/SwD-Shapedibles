<%--suppress ELValidationInspection --%>
<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8"
		 errorPage="/WEB-INF/jsp/pages/errorPage.jsp" %>
<%@ taglib uri="http://java.sun.com/jsp/jstl/core" prefix="c" %>
<!DOCTYPE html>
<html>
<head>
    <meta charset="ISO-8859-1">
    <title>Shapedibles - Registrazione</title>
    <jsp:include page="../procedural/fractalNoise.jsp"/>

    <link href="${pageContext.request.contextPath}/assets/styles/base.css" rel="stylesheet">
    <link href="${pageContext.request.contextPath}/assets/styles/pages/login-register.css" rel="stylesheet" type="text/css">
    <script src="${pageContext.request.contextPath}/assets/script/pages/register.js"></script>
</head>
<body>
<jsp:include page="../common/sticky.jsp"/>
<div class="content register">
	<div class="base glassy register">
		<h1>Registrazione</h1>
		<form id="registerForm" onsubmit="return submitFormRegister(event)">
			<div class="form-group">
				<label for="username">Username</label>
				<div class="textbox">
					<input id="username" name="username" type="text" maxlength="30" required placeholder="enter username">
				</div>
			</div>
	
			<div class="form-group">
				<label for="email">Email:</label>
				<div class="textbox">
					<input id="email" name="email" type="email" maxlength="80" required placeholder="enter email">
				</div>
			</div>

			<div class="form-group">
				<label for="nome-cognome">Nome e cognome:</label>
				<div class="textbox">
					<input id="nome-cognome" name="nome_cognome" type="text" maxlength="30" required placeholder="enter name and surname">
				</div>
			</div>

			<div class="form-group">
				<label for="password">Password:</label>
				<div class="textbox">
					<input id="password" name="password" type="password" maxlength="30" required placeholder="enter password">
				</div>
			</div>
	
			<div class="form-group">
				<label for="sesso">Sesso:</label>
				<div class="textbox">
					<select class="selectbox" id="sesso" name="sesso" required>
						<c:forEach var="gender" items="${genders}">
							<option value="${gender}">${gender}</option>
						</c:forEach>
					</select>
				</div>
			</div>

			<div class="form-group">
				<label for="paese">Paese:</label>
				<div class="textbox">
					<select class="selectbox" id="paese" name="paese" required>
						<c:forEach var="country" items="${countries}">
							<option value="${country}">${country}</option>
						</c:forEach>
					</select>
				</div>
			</div>

			<div class="form-group">
				<label for="passwordConf">Ripetere la password:</label>
				<div class="textbox">
					<input id="passwordConf" name="passwordConf" type="password" maxlength="30" required placeholder="enter password again">
				</div>
			</div>
	
			<div class="form-group">
				<label for="data-nascita">Data di Nascita:</label>
				<div class="textbox">
					<input id="data-nascita" name="data_nascita" type="date" required>
				</div>
			</div>
			<p id="registerError"></p>
			<div class="buttons">
				<div id="resetButton" class="secondary-round-btn">
					<span class="material-symbols-rounded">close</span>
					<input type="reset" value="">
				</div>
				<input class="primary-btn" id="submitBtn" type="submit" value="REGISTRATI">
			</div>
		</form>
		<a class="hyperlink" href="${pageContext.request.contextPath}/login">Sei già registrato?</a>
	</div>
</div>
<jsp:include page="../common/footer.jsp"/>
</body>
</html>