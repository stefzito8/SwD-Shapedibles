<%--suppress ELValidationInspection --%>
<%--suppress HtmlUnknownTarget --%>
<%--suppress HtmlFormInputWithoutLabel --%>
<%--suppress HtmlUnknownTarget --%>
<%--suppress ELValidationInspection --%>
<%--@elvariable id="cart" type="model.Cart"--%>
<%--suppress HtmlFormInputWithoutLabel --%>
<%@ page import="model.Cart" %>
<%
    Cart cart = (Cart) request.getSession().getAttribute("cart");
    if(cart == null)
    {
        cart = new Cart();
        request.getSession().setAttribute("cart", cart);
    }
%>
<%@ page contentType="text/html;charset=UTF-8" %>
<%@ taglib uri="http://java.sun.com/jsp/jstl/core" prefix="c" %>
<html>
<head>
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <jsp:include page="../procedural/gaussianBlur.jsp"/>
<%--    Icons--%>
    <link href="https://fonts.googleapis.com/css2?family=Merriweather+Sans:ital,wght@0,300..800;1,300..800&display=swap" rel="stylesheet">
<%--    Font--%>
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
    <link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Material+Symbols+Rounded:opsz,wght,FILL,GRAD@24,400,0,0" />
    
    <link rel="stylesheet" href="${pageContext.request.contextPath}/assets/styles/base.css">
    <link rel="stylesheet" href="${pageContext.request.contextPath}/assets/styles/pages/sticky.css">
    <script>
        var contextPath = "${pageContext.request.contextPath}/";
    </script>
    <script src="${pageContext.request.contextPath}/assets/script/utils.js"></script>
    <script src="${pageContext.request.contextPath}/assets/script/pages/sticky.js"></script>
    <title></title>
</head>
<body>
    <div id="headerSpace"></div>
    <div class="sticky">
        <header>
            <div class="header-wrapper glassy">
                <div class="header-left">
                    <div class="logo">
                        <a href="${pageContext.request.contextPath}">
                            <img src="${pageContext.request.contextPath}/assets/images/svg/logo.svg" alt="Logo" id="logoSvg">
                        </a>
                    </div>
                </div>
                <div class="header-center">
                    <div class="glassy" id="searchResultsContainer">
                        
                    </div>
                    <div id="errorSearch">
                        <label>Riempi questo campo</label>
                    </div>
                    <form class="searchbar" action="Search" method="get">
                        <input type="search" spellcheck="false" placeholder="      Cerca prodotti..." id="inputSearch" name="ricerca">
                        <button class="unclickable" type="submit" id="buttonSearch">
                            <span class="material-symbols-rounded">search</span>
                        </button>
                    </form>
                </div>
                <div class="header-right">
                    <c:choose>
                        <c:when test="${empty sessionScope['LoggedUser']}">
                            <a class="primary-round-btn nodeco profile-button" href="${pageContext.request.contextPath}/login">
                                <span class="material-symbols-rounded">login</span>
                            </a>
                        </c:when>
                        <c:otherwise>
                            <a class="secondary-round-btn nodeco profile-button" href="${pageContext.request.contextPath}/user/profile">
                                <span class="material-symbols-rounded">account_circle</span>
                            </a>
                        </c:otherwise>
                    </c:choose>
                    <a class="primary-round-btn nodeco" id="cartButton" href="${pageContext.request.contextPath}/cart">
                        <span class="material-symbols-rounded">shopping_cart</span>
                        <div id="cartCounter">
                            <span>${cart.getCartSize()}</span>
                        </div>
                    </a>
                </div>
            </div>
        </header>
    
        <div class="ruler">
            <div class="line"></div>
            <a class="handle" href="#headerSpace">
                <img src="${pageContext.request.contextPath}/assets/images/svg/handle.svg" alt="Logo">
            </a>
        </div>
    </div>
</body>
</html>
