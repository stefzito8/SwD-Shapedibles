package model.dao;

import model.bean.ProductBean;

import java.sql.SQLException;
import java.util.Collection;

public interface IProductDao {
	void doSave(ProductBean product) throws SQLException;
	
	boolean doDelete(int code) throws SQLException;
	
	ProductBean doRetrieveByKey(int code) throws SQLException;
	
	Collection<ProductBean> doRetrieveAll(String order) throws SQLException;
    
	ProductBean doRetrieveByName(String name) throws SQLException;

    Collection<ProductBean> searchByName(String query) throws SQLException;
    
    public void doUpdateInfo(int codice, int codiceInfo) throws SQLException;
}
