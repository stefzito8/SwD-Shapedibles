package model.dao;

import model.bean.ContainBean;

import java.sql.SQLException;
import java.util.Collection;

public interface IContainDao {
	public void doSave(ContainBean contain) throws SQLException;
	
	public boolean doDelete(int orderID) throws SQLException;
	
	public ContainBean doRetrieveByKey(int orderID) throws SQLException;
	
	public Collection<ContainBean> doRetrieveAll(String order) throws SQLException;
	
	public Collection<ContainBean> doRetrieveByOrder(int orderID) throws SQLException;
}
