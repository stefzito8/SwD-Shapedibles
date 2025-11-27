//Elements
let elFormLogin;
let elErrorLogin;

function submitFormLogin(event) {
    event.preventDefault();
    const formData = new FormData(elFormLogin);
    const xhr = new XMLHttpRequest();
    let animationEnd;
    xhr.open("POST", "login", true);
    xhr.setRequestHeader("X-Requested-With", "XMLHttpRequest");
    xhr.onload = async function() {
        if (this.status === 200) {
            const response = JSON.parse(this.responseText);
            await animationEnd;
            window.location.replace(response);
        }
        else
        {
            elErrorLogin.innerHTML = "Credenziali non valide";
            document.querySelector(".base").style.animation = "shake 0.5s cubic-bezier(.28, 1.63, .62, .88)";
            animationEnd = setTimeout(() => {
                elErrorLogin.innerHTML = "";
            }, 5000);
        }
    };
    document.querySelector(".base").style.animation = "slideOut 1.4s cubic-bezier(.28, 1.63, .62, .88)";
    animationEnd = setTimeout(() => {}, 900);
    console.log(formData);
    xhr.send(formData)
    return false;
}

document.addEventListener("readystatechange", () => {
    if (document.readyState === "complete") {
        mainLogin();
    }
});

function mainLogin() {
    elFormLogin = document.getElementById("loginForm");
    elErrorLogin = document.getElementById("loginError");
}