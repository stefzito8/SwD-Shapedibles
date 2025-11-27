var ImageUtils;
ImageUtils = {
    getImageWithStringInName: async function (contextPath, images, string) {
        /*
        images is an array of ImageBean objects, the img name is stored in the img property
        string is the string to search for in the img name
         */
        let baseUrl = contextPath + "assets/images/products/";
        let finalUrl;
        for (let i = 0; i < images.length; i++) {
            if (images[i].img.includes(string)) {
                finalUrl = baseUrl + images[i].img;
                break;
            }
        }

        return new Promise((resolve) => {
            let image = new Image();
            image.src = finalUrl;

            setTimeout(() => {
                if (image.width === 0) {
                    finalUrl = baseUrl + "fallback_" + string + ".jpg";
                }
                resolve(finalUrl);
            }, 500);
        });
    }
}