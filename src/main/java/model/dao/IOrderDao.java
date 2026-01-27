package model.dao;

import model.bean.ImageBean;
import model.bean.OrderBean;

import java.sql.SQLException;
import java.util.Collection;

public interface IOrderDao {

	//@ requires order != null;
	public void doSave(OrderBean order) throws SQLException;
	
	//@ requires user != null && id >= 0;
	//@ requires user.length() > 0;
	//@ ensures \result == true;
	public boolean doDelete(String user, int id) throws SQLException;
	
	//@ requires user != null && id >= 0;
	//@ requires user.length() > 0;
	//@ ensures \result != null;
	public OrderBean doRetrieveByKey(String user, int id) throws SQLException;
	
	//@ ensures \result != null;
	public Collection<OrderBean> doRetrieveAll(String order) throws SQLException;
	
	//@ requires user != null;
	//@ requires user.length() > 0;
	//@ ensures \result != null;
	public Collection<OrderBean> doRetrieveByUser(String user) throws SQLException;
}
