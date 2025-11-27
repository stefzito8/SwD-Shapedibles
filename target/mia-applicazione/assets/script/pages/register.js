//Elements
let elFormRegister;
let elErrorRegister;

function errorRegister(message = "Qualcosa è andato storto, verifica i dati inseriti") {
    elErrorRegister.innerHTML = message;
    document.querySelector(".base").style.animation = "shake 0.5s cubic-bezier(.28, 1.63, .62, .88)";
    animationEnd = setTimeout(() => {
        elErrorRegister.innerHTML = "";
    }, 5000);
    return false;
}

function registerValidation(formData) {
    console.log(formData);
    const email = formData.get("email");
    const password = formData.get("password");
    const confirmPassword = formData.get("passwordConf");
    const nameSurname = formData.get("nome_cognome");
    const birthDate = formData.get("data_nascita");
    if (password !== confirmPassword)
        return errorRegister("Le password non corrispondono");
    if (password.length < 8)
        return errorRegister("La password deve essere di almeno 8 caratteri");
    if (!email.includes("@"))
        return errorRegister("Email non valida");
    if (validateBirthDate(birthDate) === false)
        return errorRegister("Data di nascita non valida (16 anni età minima)");
    if (nameSurname.split(" ").length < 2)
        return errorRegister("Inserisci nome e cognome");
    
    return true;

    function validateBirthDate(inputDate) {
        const currentDate = new Date();
        const userDate = new Date(inputDate);

        // Check if userDate is a valid date and is not in the future
        if (userDate === undefined || userDate === null || userDate > currentDate) {
            return false;
        }
        // Example: Ensure the user is at least 16 years old
        const minAgeDate = new Date();
        minAgeDate.setFullYear(minAgeDate.getFullYear() - 16);
        return userDate <= minAgeDate;
        
    }
}

function submitFormRegister(event) {
    event.preventDefault();
    const formData = new FormData(elFormRegister);
    for (const pair of formData.entries()) {
        console.log(pair[0], pair[1]);
    }
    if (!registerValidation(formData))
        return;
    const xhr = new XMLHttpRequest();
    let animationEnd;
    xhr.open("POST", "register", true);
    xhr.setRequestHeader("X-Requested-With", "XMLHttpRequest");
    xhr.onload = async function() {
        if (this.status === 200) {
            const response = JSON.parse(this.responseText);
            await animationEnd;
            window.location.replace(response);
        }
        else if (this.status === 401) {
            const response = JSON.parse(this.responseText);
            errorRegister(response);
        }
        else
            errorRegister();
    };
    document.querySelector(".base").style.animation = "slideOut 1.4s cubic-bezier(.28, 1.63, .62, .88)";
    animationEnd = setTimeout(() => {}, 900);
    console.log(formData);
    xhr.send(formData)
    return false;
}

document.addEventListener("readystatechange", () => {
    if (document.readyState === "complete") {
        mainRegister();
    }
});

function mainRegister() {
    elFormRegister = document.getElementById("registerForm");
    elErrorRegister = document.getElementById("registerError");
}