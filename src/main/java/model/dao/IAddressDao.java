 package model.dao;

import model.bean.AddressBean;

import java.sql.SQLException;
import java.util.Collection;

public interface IAddressDao {
    public void doSave(AddressBean address) throws SQLException;
	
	public boolean doDelete(String id, String user) throws SQLException;
	
	public AddressBean doRetrieveByKey(String id, String user) throws SQLException;
	
	public Collection<AddressBean> doRetrieveAll(String order) throws SQLException;
	
	public Collection<AddressBean> doRetrieveByUser(String user) throws SQLException;
}
