let productPage;
let elProductPageCartQuantity;
let elProductPageCartPlus;
let elProductPageCartMinus;

function productById(id) {
    const xhr = new XMLHttpRequest();
    xhr.open("GET", "search?id=" + encodeURIComponent(id), true);
    xhr.setRequestHeader("X-Requested-With", "XMLHttpRequest");
    xhr.onload = function() {
        if (this.status === 200) {
            productPage = JSON.parse(this.responseText);
            productPage.cartQuantity = elProductPageCartQuantity.value;
        }
    };
    xhr.send();
}

document.addEventListener("readystatechange", () => {
    if (document.readyState === "complete") {
        mainProductDetails();
    }
});

function mainProductDetails() {
    elProductPageCartPlus = document.getElementById("productCartPlus");
    elProductPageCartMinus = document.getElementById("productCartMinus");
    elProductPageCartQuantity = document.getElementById("cartProductQuantity");
    
    productById()
    
    window.addEventListener('scroll', () => {
        document.body.style.setProperty('--scroll', (window.pageYOffset / (document.body.offsetHeight - window.innerHeight)).toString());
    }, false);

    elProductPageCartPlus.addEventListener("click", () => productCartAction("addC", productPage, elProductPageCartQuantity));
    elProductPageCartMinus.addEventListener("click", () => productCartAction("deleteC", productPage, elProductPageCartQuantity));
}