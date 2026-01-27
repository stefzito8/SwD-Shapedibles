package model.datasource;


import model.bean.ContainBean;
import model.dao.IContainDao;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Collection;
import java.util.LinkedList;

public class ContainDaoDataSource implements IContainDao {
	
	static private final String TABLE_NAME="Contains";
	//@ spec_public non_null
	private DataSource ds;
	
	//@ public invariant ds != null;

	//@ requires ds != null;
	//@ ensures this.ds == ds;
	public ContainDaoDataSource(DataSource ds) 
	{
		this.ds=ds;
		System.out.println("DriverManager Product Model creation....");
	}
	
	@Override
	public void doSave(ContainBean contain) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		String insertSQL="INSERT INTO " + ContainDaoDataSource.TABLE_NAME 
				+ " (order_code, info_code, quantity) VALUES (?,?,?)";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(insertSQL);
			preparedStatement.setInt(1, contain.getCodiceOrdine());
			preparedStatement.setInt(2, contain.getCodiceProdotto());
			preparedStatement.setInt(3, contain.getQuantità());

			
			preparedStatement.executeUpdate();
		} 
		finally {
			try {
				if (preparedStatement != null)
					 preparedStatement.close();
			} finally {
				connection.close();;
			}
		}
	}

	@Override
	public boolean doDelete(int orderID) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		int result = 0;
		
		String deleteSQL = "DELETE FROM " + ContainDaoDataSource.TABLE_NAME + " WHERE order_code = ?";
		
		try {
			connection= ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(deleteSQL);
			preparedStatement.setInt(1, orderID);
			
			
			result = preparedStatement.executeUpdate();
			//@ assert result >= 0;
		} finally {
			try {
				if (preparedStatement != null)
					preparedStatement.close();
			} finally {
				connection.close();
			}
		}
		return (result!=0);
	}

	@Override
	public ContainBean doRetrieveByKey(int orderID) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		ContainBean bean= new ContainBean();
		//@ assert bean != null;
		String selectSQL = "SELECT * FROM " + ContainDaoDataSource.TABLE_NAME + " WHERE order_code = ?";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setInt(1, orderID);
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;
			while(rs.next()) {
				bean.setCodiceOrdine(rs.getInt("order_code"));
				bean.setCodiceProdotto(rs.getInt("info_code"));
				bean.setQuantità(rs.getInt("Quantity"));
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		//@ assert bean != null;
		return bean;
	}

	@Override
	public Collection<ContainBean> doRetrieveAll(String order) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		Collection<ContainBean> items= new LinkedList<ContainBean>();
		//@ assert items != null && items.isEmpty();
		String selectSQL = "SELECT * FROM " + ContainDaoDataSource.TABLE_NAME;
		
		if(order != null && !order.equals("")) {
			selectSQL +=" ORDER BY " + order;
		}
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;
			/*@ 
			  @ loop_invariant items != null;
			  @*/
			while(rs.next()) {
				ContainBean  bean = new ContainBean();
				
				bean.setCodiceOrdine(rs.getInt("order_code"));
				bean.setCodiceProdotto(rs.getInt("info_code"));
				bean.setQuantità(rs.getInt("Quantity"));
				//@ assert bean != null;
				items.add(bean);
				//@ assert !items.isEmpty();
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		
		return items;
	}

	@Override
	public Collection<ContainBean> doRetrieveByOrder(int orderID) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		Collection<ContainBean> items= new LinkedList<ContainBean>();
		//@ assert items != null && items.isEmpty();
		String selectSQL = "SELECT * FROM " + ContainDaoDataSource.TABLE_NAME + " WHERE order_code = ?";
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setInt(1, orderID);
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;

			/*@
			@ loop_invariant items != null;
			@*/
			while(rs.next()) {
				ContainBean  bean = new ContainBean();
				
				bean.setCodiceOrdine(rs.getInt("order_code"));
				bean.setCodiceProdotto(rs.getInt("info_code"));
				bean.setQuantità(rs.getInt("Quantity"));
				//@ assert bean != null;
				items.add(bean);
				//@ assert !items.isEmpty();
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		
		return items;
	}

}
