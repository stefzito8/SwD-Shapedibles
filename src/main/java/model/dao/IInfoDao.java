package model.dao;

import java.sql.SQLException;
import java.util.Collection;

import model.bean.InfoBean;

public interface IInfoDao {
	
    public void doSave(InfoBean product) throws SQLException;
	
	public boolean doDelete(int code) throws SQLException;
	
	public InfoBean doRetrieveByKey(int code) throws SQLException;
	
	public Collection<InfoBean> doRetrieveAll(String order) throws SQLException;
	
	public InfoBean doRetrieveByName(String name) throws SQLException;
	
	public void doUpdateQuantity(int codice, int quantity) throws SQLException;
}
