// noinspection JSUnresolvedReference
let scrollTimeout;
let scrollPos;
let hideSearchResultsTimeout;
let currentSearchRequest;
//Elements
let elInputSearch;
let elSearchBar;
let elButtonSearch;
let elErrorSearch;
let elSearchResults;
let elCartButton;
let elBody;
let elHeader;
let elHeaderSpace
//Utils
let mouseOnSearchResults //Used to avoid hiding search results when mouse is over them

function updateScroller() {
    const scrollY = window.scrollY;
    const viewportHeight = window.innerHeight;
    const documentHeight = document.documentElement.scrollHeight;
    const handle = document.querySelector(".handle");
    const line = document.querySelector(".line");

    scrollPos = Math.round((scrollY / (documentHeight - viewportHeight)) * 75);

    line.style.height = scrollPos + "vh"
    handle.style.opacity = line.style.opacity = "100%";

    clearTimeout(scrollTimeout);
    
    scrollTimeout = setTimeout(() => {
        if (scrollPos === 0) 
            handle.style.opacity = "0%";
        else
            line.style.opacity = "20%";
            handle.style.opacity = "";
    }, 300);
}

function searchInputChange() {
    const searchQuery = elInputSearch.value.trim();
    if (searchQuery.length > 0) {
        if (currentSearchRequest)
            currentSearchRequest.abort();
        currentSearchRequest = new XMLHttpRequest();
        currentSearchRequest.open("GET", "search?ricerca=" + encodeURIComponent(searchQuery), true);
        currentSearchRequest.setRequestHeader("X-Requested-With", "XMLHttpRequest");
        currentSearchRequest.onload = function() {
            if (this.status === 200) {
                const results = JSON.parse(this.responseText);
                // Update UI with results
                updateSearchResults(results);
            }
        };
        currentSearchRequest.send();
    }
    else
        clearSearchResults(true);
    
    elSearchBar.style.boxShadow = "0 0 15px rgba(255, 255, 255, 0.20),inset 0 0 30px rgba(0, 0, 0, 0.16)";
    setTimeout(() => {
        elSearchBar.style.boxShadow = "0 0 5px rgba(255, 255, 255, 0), inset 0 0 30px rgba(0, 0, 0, 0.16)";
    }, 400);
}

async function clearSearchResults(changeHeight) {
    elSearchResults.innerHTML = "";
    if (changeHeight)
    {
        await heightSearchResults(0);
        elSearchResults.classList.remove("loaded");
    }
    elBody.classList.remove("blurred-overlay");
}

function heightSearchResults(newHeight) {
    return new Promise((resolve) => {
        let currentHeight = elSearchResults.offsetHeight;
        const steps = 20;
        let step = 0;
        const stepHeight = (newHeight - currentHeight) / steps;

        function animateHeight() {
            if (step < steps) {
                currentHeight += stepHeight;
                elSearchResults.style.height = `${currentHeight}px`;
                step++;
                requestAnimationFrame(animateHeight);
            } else {
                resolve(); // Resolve the promise when animation is complete
            }
        }

        requestAnimationFrame(animateHeight);
    });
}

function productCartAction(action, product, elResultCartQuantity) {
    /*
    *   action: "addC" or "deleteC"
     */
    if (action === "addC" && 
        (product.cartQuantity + 1) > product.info.disponibilità)
        return;
    if (action === "deleteC" && product.cartQuantity === 0)
        return;
    
    const xhr = new XMLHttpRequest();
    xhr.open("POST", "Cart", true);
    xhr.setRequestHeader("Content-Type", "application/x-www-form-urlencoded");
    xhr.setRequestHeader("X-Requested-With", "XMLHttpRequest");

    const requestBody = `action=${action}&id=${encodeURIComponent(product.codice)}`;

    xhr.onload = function() {
        if (this.status === 200) {
            response = JSON.parse(this.responseText);
            if (!response) return;
            
            switch (action) {
                case "addC":
                    product.cartQuantity++;
                    break;
                case "deleteC":
                    product.cartQuantity--;
                    break;
            }
            elResultCartQuantity.textContent = product.cartQuantity.toString();
            let elCartCounter = document.querySelector("#cartCounter");
            elCartCounter.classList.add("counter-change");
            setTimeout(() => { elCartCounter.classList.remove("counter-change"); }, 850);
            elCartCounter.querySelector("span").textContent = response.cartSize.toString();
        }
    };
    xhr.send(requestBody);
}

async function updateSearchResults(results) {
    await clearSearchResults(false);

    if (!results || Object.keys(results).length === 0) {
        return;
    }

    let newHeight = 0;

    for (const product of results) {
        // Directly access product properties, assuming product is already an object
        const elResultDiv = document.createElement("div");
        const elResultImg = document.createElement("img");
        const elResultCart = document.createElement("div");
        const elResultCartPlus = document.createElement("button");
        const elResultCartMinus = document.createElement("button");
        const elResultCartQuantity = document.createElement("div");
        const elResultInfo = document.createElement("div");
        const elResultName = document.createElement("p");
        const elResultDesc = document.createElement("span");
        const elResultQuantity = document.createElement("div");
        
        console.log(product);
        
        elResultDiv.classList.add("search-result");
        
        elResultImg.src = await ImageUtils.getImageWithStringInName(contextPath, product.immagini, "square");
        
        elResultCart.classList.add("cart-controls");
        elResultCartPlus.id = "cartPlus";
        elResultCartPlus.textContent = "+";
        elResultCartMinus.id = "cartMinus";
        elResultCartMinus.textContent = "-";
        elResultCartQuantity.id = "cartQuantity";

        elResultCartPlus.addEventListener("click", () => productCartAction("addC", product, elResultCartQuantity));
        elResultCartMinus.addEventListener("click", () => productCartAction("deleteC", product, elResultCartQuantity));

        elResultCart.appendChild(elResultCartPlus);
        elResultCart.appendChild(elResultCartQuantity);
        elResultCart.appendChild(elResultCartMinus);

        elResultCartQuantity.textContent = product.cartQuantity.toString();
        
        elResultName.textContent = product.nome; // Directly access property
        elResultDesc.textContent = product.info.descrizione;
        elResultDesc.classList.add("desc");
        
        elResultQuantity.textContent = product.info.disponibilità + " disponibili";
        elResultQuantity.classList.add("quantity");
        
        elResultInfo.classList.add("info");
        elResultInfo.appendChild(elResultName);
        elResultInfo.appendChild(elResultDesc);
        
        elResultImg.appendChild(elResultQuantity);

        elResultDiv.appendChild(elResultImg);
        elResultDiv.appendChild(elResultCart);
        elResultDiv.appendChild(elResultInfo);
        
        let toProduct = () => {
            window.location.assign(contextPath + "ProductDetails?product=" + product.codice);
        }
        
        elResultName.addEventListener("click", toProduct);
        elResultImg.addEventListener("click", toProduct);

        elSearchResults.appendChild(elResultDiv);
        newHeight += elResultDiv.offsetHeight;
    }

    const elSpacer = document.createElement("div");
    elSpacer.classList.add("spacer");
    elSearchResults.insertBefore(elSpacer, elSearchResults.firstChild);
    elSearchResults.appendChild(elSpacer.cloneNode());

    newHeight += elSpacer.offsetHeight * 2;

    await heightSearchResults(newHeight);

    void elSearchResults.offsetHeight; // Force reflow
    elSearchResults.classList.remove("glassy");
    elSearchResults.classList.add("glassy");
    
    elSearchResults.classList.add("loaded");
    elBody.classList.add("blurred-overlay");

}

function searchError(error) {
    elErrorSearch.children[0].textContent = error;
    elErrorSearch.style.opacity = "100%";
    setTimeout(() => {
        elErrorSearch.style.opacity = "0%";
    }, 700)
}

function adjustHeaderSpace() {
    const headerHeight = elHeader.offsetHeight;
    elHeaderSpace.style.height = headerHeight + 'px';
}

document.addEventListener("readystatechange", () => {
    if (document.readyState === "complete") {
        mainSticky();
    }
});

function mainSticky() {
    //Elements
    elInputSearch = document.getElementById("inputSearch");
    elSearchBar = document.getElementsByClassName("searchbar")[0];
    elButtonSearch = document.getElementById("buttonSearch");
    elErrorSearch = document.getElementById("errorSearch");
    elSearchResults = document.getElementById("searchResultsContainer");
    elCartButton = document.getElementById("cartButton");
    elBody = document.querySelector("body");
    elHeader = document.querySelector("header");
    elHeaderSpace = document.querySelector("#headerSpace");

    adjustHeaderSpace();
    
    //Scroll ruler animation
    window.addEventListener("scroll", updateScroller);
    window.addEventListener("resize", () => {
        updateScroller();
        adjustHeaderSpace();
    });
    
    //Searchbar animation and advanced styling
    elInputSearch.addEventListener("input", () => searchInputChange());
    elInputSearch.addEventListener("focus", () => {
        elButtonSearch.style.left = `calc(99% - ${elButtonSearch.offsetWidth}px)`;
        clearTimeout(hideSearchResultsTimeout);
        searchInputChange();
    });
    elInputSearch.addEventListener("blur", () => {
        elButtonSearch.style.left = '1%';
        if (mouseOnSearchResults) return;
        hideSearchResultsTimeout = setTimeout(async () => {
            await clearSearchResults(true);
            }, 1000);
    });
    elSearchResults.addEventListener("mouseenter", () => {
        mouseOnSearchResults = true;
        clearTimeout(hideSearchResultsTimeout);
    });
    elSearchResults.addEventListener("mouseleave", () => { 
        if (!mouseOnSearchResults) return; //To avoid hiding search results when mouse exits search results but may be focused on inputbox
        if (elInputSearch !== document.activeElement) 
            hideSearchResultsTimeout = setTimeout(async () => { 
                await clearSearchResults(true);
                }, 1000); 
    });
    
    //Searchbar query validation
    elSearchBar.addEventListener('submit', (event) => {
        const searchQuery = elInputSearch.value.trim();
        
        if (searchQuery === '') {
            event.preventDefault();
            searchError('Inserisci un valore di ricerca');
        }

        if (!/^[a-zA-Z0-9 ]+$/.test(searchQuery)) {
            event.preventDefault();
            searchError('Caratteri non validi');
        }
    });
    
    updateScroller();
}

