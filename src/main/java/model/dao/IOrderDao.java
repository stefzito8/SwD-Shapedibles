package model.dao;

import model.bean.ImageBean;
import model.bean.OrderBean;

import java.sql.SQLException;
import java.util.Collection;

public interface IOrderDao {
	public void doSave(OrderBean order) throws SQLException;
	
	public boolean doDelete(String user, int id) throws SQLException;
	
	public OrderBean doRetrieveByKey(String user, int id) throws SQLException;
	
	public Collection<OrderBean> doRetrieveAll(String order) throws SQLException;
	
	public Collection<OrderBean> doRetrieveByUser(String user) throws SQLException;
}
