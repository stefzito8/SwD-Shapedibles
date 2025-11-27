let elForm;

function DoSubmit() {

	const user = elForm.user.value;
	const dateMax = elForm.dateMax.value;
	const dateMin = elForm.dateMin.value;

	let actionValue = "UserFilter";

	if(user !== "" && (dateMin !== "" || dateMax !== "")) {
		actionValue = "User-DateFilter";
	} else if(user !== "" && dateMin === "" && dateMax === "") {
		actionValue = "UserFilter";
	} else if(user === "" && (dateMin !== "" || dateMax !== "")) {
		actionValue = "DateFilter";
	}
	
	elForm.querySelector("input").value = actionValue;
	
	elForm.submit();
}

document.onreadystatechange = () => {
	if (document.readyState === "complete") {
		main();
	}
};

function main() {
	elForm = document.getElementById("filterForm");
	
	elForm.addEventListener('submit', (event) => {
		event.preventDefault();
		DoSubmit();
	});
}