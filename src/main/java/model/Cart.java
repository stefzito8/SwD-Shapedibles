package model;

import model.bean.ProductBean;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

public class Cart {

	private final Map<ProductBean, Integer> products;

	public Cart() {
		products = new HashMap<>();
	}

	public void addProduct(ProductBean product) {
		System.out.println(products.getOrDefault(product, 0) + 1);
		products.put(product, products.getOrDefault(product, 0) + 1);
		System.out.println(products.getOrDefault(product, 0));
	}

	public void deleteProduct(ProductBean product) {
		if (products.containsKey(product)) {
			int quantity = products.get(product) - 1;
			if (quantity > 0) {
				products.put(product, quantity);
			} else {
				products.remove(product);
			}
		}
	}

	public Collection<ProductBean> getProducts() {
		return new ArrayList<>(products.keySet());
	}
	
	public void ClearCart() {
		products.clear();
	}

	public int getProductQuantity(ProductBean product) {
		return products.getOrDefault(product, 0);
	}
	
	public Map<ProductBean,Integer> getProductQuantity (Collection<ProductBean> products){
		Map<ProductBean,Integer> map = new HashMap<>();
		for(ProductBean product : products) {
			map.put(product, getProductQuantity(product));
		}
		return map;
	}

	public Map<ProductBean,Integer> getProductQuantities (){
		return getProductQuantity(products.keySet());
	}

	public int getCartSize() {
		return products.values().stream().mapToInt(Integer::intValue).sum();
	}
}