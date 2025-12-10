package model.dao;

import model.bean.ContainBean;

import java.sql.SQLException;
import java.util.Collection;

public interface IContainDao {

	//@ requires contain != null;
	public void doSave(ContainBean contain) throws SQLException;
	
	//@ requires orderID >= 0;
	//@ ensures \result == true;
	public boolean doDelete(int orderID) throws SQLException;
	
	//@ requires orderID >= 0;
	//@ ensures \result != null;
	public ContainBean doRetrieveByKey(int orderID) throws SQLException;
	
	//@ ensures \result != null;
	public Collection<ContainBean> doRetrieveAll(String order) throws SQLException;
	
	//@ requires orderID >= 0;
	//@ ensures \result != null;  
	public Collection<ContainBean> doRetrieveByOrder(int orderID) throws SQLException;
}
