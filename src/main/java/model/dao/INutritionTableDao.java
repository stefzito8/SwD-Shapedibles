package model.dao;

import model.bean.NutritionTableBean;

import java.sql.SQLException;
import java.util.Collection;

public interface INutritionTableDao {
	public void doSave(NutritionTableBean nutritionTable) throws SQLException;
	
	public boolean doDelete(int productID) throws SQLException;
	
	public NutritionTableBean doRetrieveByKey(int productID) throws SQLException;
	
	public Collection<NutritionTableBean> doRetrieveAll(String order) throws SQLException;
	
}
