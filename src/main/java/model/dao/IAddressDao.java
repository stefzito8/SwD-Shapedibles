 package model.dao;

import model.bean.AddressBean;

import java.sql.SQLException;
import java.util.Collection;

public interface IAddressDao {
	//@ requires address != null;
    public void doSave(AddressBean address) throws SQLException;
	
	//@ requires user != null && id != null;
	//@ requires user.length() > 0;
	//@ requires id.length() > 0;
	//@ ensures \result == true;
	public boolean doDelete(String id, String user) throws SQLException;
	
	//@ requires user != null && id != null;
	//@ requires user.length() > 0;
	//@ requires id.length() > 0;
	//@ ensures \result != null; 
	public AddressBean doRetrieveByKey(String id, String user) throws SQLException;
	
	//@ ensures \result != null;
	public Collection<AddressBean> doRetrieveAll(String order) throws SQLException;
	
	//@ requires user != null;
	//@ requires user.length() > 0;
	//@ ensures \result != null;
	public Collection<AddressBean> doRetrieveByUser(String user) throws SQLException;
}
