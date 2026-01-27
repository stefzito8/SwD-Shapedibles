package model.dao;

import model.bean.UserBean;

import java.sql.SQLException;
import java.util.Collection;

public interface IUserDao {
	//@ requires user != null; 
    public void doSave(UserBean user) throws SQLException;
	
	//@ requires username != null;
	//@ requires username.length() > 0;
	//@ ensures \result == true;
	public boolean doDelete(String username) throws SQLException;
	
	//@ requires username != null;
	//@ requires username.length() > 0;
	//@ ensures \result != null;
	public UserBean doRetrieveByKey(String username) throws SQLException;
	
	//@ ensures \result != null;
	public Collection<UserBean> doRetrieveAll(String order) throws SQLException;
}
