<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" errorPage="/WEB-INF/jsp/pages/errorPage.jsp" %>
<!DOCTYPE html>
<html>
<head>
    <meta charset="ISO-8859-1">
    <title>Shapedibles - Login</title>
    <jsp:include page="../procedural/fractalNoise.jsp"/>

    <link href="${pageContext.request.contextPath}/assets/styles/base.css" rel="stylesheet">
    <link href="${pageContext.request.contextPath}/assets/styles/pages/login-register.css" rel="stylesheet" type="text/css">
    <script src="${pageContext.request.contextPath}/assets/script/pages/login.js"></script>
</head>
<body>
<jsp:include page="../common/sticky.jsp"/>
<div class="content login">
    <div class="base glassy login">
        <h1> Login </h1>
        <form id="loginForm" onsubmit="return submitFormLogin(event)">
            <label for="username">Username</label>
            <div class="textbox">
                <input id="username" name="username" type="text" maxlength="30" required placeholder="Il tuo username">
            </div>
            <label for="password">Password</label>
            <div class="textbox">
                <input id="password" name="password" type="password" maxlength="30" required placeholder="La tua password">
            </div>
            <p id="loginError"></p>
            <div class="buttons">
                <div id="resetButton" class="secondary-round-btn">
                    <span class="material-symbols-rounded">close</span>
                    <input type="reset" value="">
                </div>

                <input class="primary-btn" id="submitBtn" type="submit" value="ACCEDI">
            </div>
        </form>
        <a class="hyperlink" href="${pageContext.request.contextPath}/register">Vuoi registrarti?</a>
    </div>
</div>
<jsp:include page="../common/footer.jsp"/>
</body>
</html>