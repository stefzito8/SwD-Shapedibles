package model.dao;

import model.bean.NutritionTableBean;

import java.sql.SQLException;
import java.util.Collection;

public interface INutritionTableDao {
	
	//@ requires nutritionTable != null;
	public void doSave(NutritionTableBean nutritionTable) throws SQLException;
	
	//@ requires productID >= 0;
	//@ ensures \result == true;
	public boolean doDelete(int productID) throws SQLException;
	
	//@ requires productID >= 0;	
	//@ ensures \result != null;
	public NutritionTableBean doRetrieveByKey(int productID) throws SQLException;
	
	//@ ensures \result != null;
	public Collection<NutritionTableBean> doRetrieveAll(String order) throws SQLException;
	
}
