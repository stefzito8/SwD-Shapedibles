package model.dao;

import java.sql.SQLException;
import java.util.Collection;

import model.bean.ImageBean;

public interface IImageDao {
    
	//@ requires image != null;
	public void doSave(ImageBean image) throws SQLException;
	
	//@ requires num >= 0 && codice >= 0;
	//@ ensures \result == true;
	public boolean doDelete(int num, int codice) throws SQLException;
	
	//@ requires num >= 0 && codice >= 0;
	//@ ensures \result != null;
	public ImageBean doRetrieveByKey(int codice, int num) throws SQLException;
	
	//@ ensures \result != null;
	public Collection<ImageBean> doRetrieveAll(String order) throws SQLException;
	
	//@ requires codice >= 0;
	//@ ensures \result != null;
	public Collection<ImageBean> doRetrieveByProduct(int codice) throws SQLException;
}
