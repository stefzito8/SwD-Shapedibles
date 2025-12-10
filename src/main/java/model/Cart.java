package model;

import model.bean.ProductBean;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

public class Cart {

	//@ spec_public
	private final Map<ProductBean, Integer> products;

	//@ public invariant products != null;

	//@ ensures products != null && products.isEmpty();
	public Cart() {
		products = new HashMap<>();
	}

	//@ requires product != null;
	/*@ 
      @ ensures (\old(products.containsKey(product)) 
      @     ==> products.containsKey(product) && products.get(product) == \old(products.get(product)) + 1);
      @
      @ ensures (!\old(products.containsKey(product))) 
      @     ==> products.containsKey(product) && products.get(product) == 1;
      @*/
	public void addProduct(ProductBean product) {
		//@ assume products.getOrDefault(product, 0) < Integer.MAX_VALUE;
		System.out.println(products.getOrDefault(product, 0) + 1);
		//@ assume products.getOrDefault(product, 0) < Integer.MAX_VALUE;
		products.put(product, products.getOrDefault(product, 0) + 1);
		//@ assume products.getOrDefault(product, 0) < Integer.MAX_VALUE;
		System.out.println(products.getOrDefault(product, 0));
	}

	//@ requires product != null;
	/*@ 
      @ ensures (\old(products.containsKey(product)) && \old(products.get(product)) > 1) 
      @     ==> products.containsKey(product) && products.get(product) == \old(products.get(product)) - 1;
      @
      @ ensures (\old(products.containsKey(product)) && \old(products.get(product)) == 1) 
      @     ==> !products.containsKey(product);
      @
      @ ensures (!\old(products.containsKey(product))) 
      @     ==> !products.containsKey(product);
      @*/
	public void deleteProduct(ProductBean product) {
		if (products.containsKey(product)) {
			int quantity = products.get(product) - 1;
			if (quantity > 0) {
				//@ assume products.get(product) != null;
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