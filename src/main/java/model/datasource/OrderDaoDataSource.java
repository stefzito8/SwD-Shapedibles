package model.datasource;


import model.bean.OrderBean;
import model.dao.IOrderDao;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Collection;
import java.util.LinkedList;

public class OrderDaoDataSource implements IOrderDao
{
	private static final String TABLE_NAME="orders";
	//@ spec_public non_null
	private DataSource ds;
	
	//@ public invariant ds != null;

	//@ requires ds != null;
	//@ ensures this.ds == ds;
	public OrderDaoDataSource(DataSource ds)
	{
		this.ds=ds;
		System.out.println("DriverManager Product Model creation....");
	}
	
	@Override
	public void doSave(OrderBean order) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/ Connection connection = null;
		/*@ nullable @*/ PreparedStatement preparedStatement = null;
		
		String insertSQL="INSERT INTO " + OrderDaoDataSource.TABLE_NAME 
				+ " (\"User\", code, address, state, order_date, total_cost) VALUES (?,?,?,?,?,?)";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(insertSQL);
			preparedStatement.setString(1, order.getUtente());
			preparedStatement.setInt(2, order.getCodice());
			preparedStatement.setString(3, order.getIndirizzo());
			preparedStatement.setString(4, order.getStato());
			preparedStatement.setString(5, order.getDataOrdine());
			preparedStatement.setDouble(6, order.getSaldoTotale());

			
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
	public boolean doDelete(String user, int id) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/ Connection connection = null;
		/*@ nullable @*/ PreparedStatement preparedStatement = null;
		
		int result = 0;
		
		String deleteSQL = "DELETE FROM " + OrderDaoDataSource.TABLE_NAME + " WHERE CODE = ? AND USER = ?";
		
		try {
			connection= ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(deleteSQL);
			preparedStatement.setInt(1, id);
			preparedStatement.setString(2, user);
			
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
	public OrderBean doRetrieveByKey(String user, int id) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/ Connection connection = null;
		/*@ nullable @*/ PreparedStatement preparedStatement = null;
		
		OrderBean bean= new OrderBean();
		//@ assert bean != null;
		String selectSQL = "SELECT * FROM " + OrderDaoDataSource.TABLE_NAME + " WHERE CODE = ? AND USER = ?";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setInt(1, id);
			preparedStatement.setString(2, user);
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;
			
			while(rs.next()) {
				bean.setUtente(rs.getString("User"));
				bean.setCodice(rs.getInt("code"));
				bean.setIndirizzo(rs.getString("address"));
				bean.setStato(rs.getString("state"));
				bean.setDataOrdine(rs.getString("order_date"));
				bean.setSaldoTotale(rs.getDouble("total_cost"));
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
	public Collection<OrderBean> doRetrieveAll(String order) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/ Connection connection = null;
		/*@ nullable @*/ PreparedStatement preparedStatement = null;
		
		Collection<OrderBean> orders= new LinkedList<OrderBean>();
		//@ assert orders != null && orders.isEmpty();
		String selectSQL = "SELECT * FROM " + OrderDaoDataSource.TABLE_NAME;
		
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
              @ loop_invariant orders != null;
              @*/
			while(rs.next()) {
				OrderBean  bean = new OrderBean();
				
				bean.setUtente(rs.getString("User"));
				bean.setCodice(rs.getInt("code"));
				bean.setIndirizzo(rs.getString("address"));
				bean.setStato(rs.getString("state"));
				bean.setDataOrdine(rs.getString("order_date"));
				bean.setSaldoTotale(rs.getDouble("total_cost"));
				//@ assert bean != null;
				orders.add(bean);
				//@ assert !orders.isEmpty();
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		
		return orders;
	}

	@Override
	public Collection<OrderBean> doRetrieveByUser(String user) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		Collection<OrderBean> orders= new LinkedList<OrderBean>();
		//@ assert orders != null && orders.isEmpty();
		String selectSQL = "SELECT * FROM " + OrderDaoDataSource.TABLE_NAME + " WHERE USER= ? ";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setString(1, user);
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;

			/*@ 
              @ loop_invariant orders != null;
              @*/
			while(rs.next()) {
				OrderBean  bean = new OrderBean();
				
				bean.setUtente(rs.getString("User"));
				bean.setCodice(rs.getInt("code"));
				bean.setIndirizzo(rs.getString("address"));
				bean.setStato(rs.getString("state"));
				bean.setDataOrdine(rs.getString("order_date"));
				bean.setSaldoTotale(rs.getDouble("total_cost"));
				//@ assert bean != null;
				orders.add(bean);
				//@ assert !orders.isEmpty();
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		
		return orders;
	}
	
}
