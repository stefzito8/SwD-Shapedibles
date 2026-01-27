package model.dao;

import model.bean.ProductBean;

import java.sql.SQLException;
import java.util.Collection;

public interface IProductDao {

	//@ requires product != null;
	void doSave(ProductBean product) throws SQLException;
	
	//@ requires code >= 0;
	//@ ensures \result == true;
	boolean doDelete(int code) throws SQLException;
	
	//@ requires code >= 0;
	//@ ensures \result != null;
	ProductBean doRetrieveByKey(int code) throws SQLException;
	
	//@ ensures \result != null;
	Collection<ProductBean> doRetrieveAll(String order) throws SQLException;
    
	//@ requires name != null;
	//@ requires name.length() > 0;
	//@ ensures \result != null;
	ProductBean doRetrieveByName(String name) throws SQLException;

	//@ requires query != null;
	//@ requires query.length() > 0;
	//@ ensures \result != null;
    Collection<ProductBean> searchByName(String query) throws SQLException;
    
	//@ requires  codice>=0 && codiceInfo>= 0;
    public void doUpdateInfo(int codice, int codiceInfo) throws SQLException;
}
