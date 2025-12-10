package model.dao;

import java.sql.SQLException;
import java.util.Collection;

import model.bean.InfoBean;

public interface IInfoDao {
	
	//@ requires product != null;
    public void doSave(InfoBean product) throws SQLException;
	
	//@ requires code >= 0;
	public boolean doDelete(int code) throws SQLException;
	
	//@ requires code >= 0;
	//@ ensures \result != null;
	public InfoBean doRetrieveByKey(int code) throws SQLException;
	
	//@ ensures \result != null;
	public Collection<InfoBean> doRetrieveAll(String order) throws SQLException;
	
	//@ requires name != null;
	//@ requires name.length() > 0;
	//@ ensures \result != null;
	public InfoBean doRetrieveByName(String name) throws SQLException;
	
	//@ requires  codice>=0 && quantity >= 0;
	public void doUpdateQuantity(int codice, int quantity) throws SQLException;
}
