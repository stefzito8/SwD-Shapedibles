package model.datasource;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Collection;
import java.util.LinkedList;

import javax.sql.DataSource;

import model.bean.InfoBean;
import model.dao.IInfoDao;

public class InfoDaoDataSource implements IInfoDao {
	private static final String TABLE_NAME = "product_info";
	private DataSource ds= null;
	
	public InfoDaoDataSource(DataSource ds)
	{
		this.ds=ds;
		System.out.println("DriverManager info Model creation....");
	}
	
	@Override
	public void doSave(InfoBean info) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		String insertSQL="INSERT INTO " + InfoDaoDataSource.TABLE_NAME 
				+ " (name, price, description, availability , type) VALUES (?,?,?,?,?)";
		
		try {
			connection = ds.getConnection();
			preparedStatement = connection.prepareStatement(insertSQL);
			preparedStatement.setString(1, info.getNome());
			preparedStatement.setDouble(2, info.getCosto());
			preparedStatement.setString(3, info.getDescrizione());
			preparedStatement.setInt(4, info.getDisponibilità());
			preparedStatement.setString(5, info.getTipologia());
			
			preparedStatement.executeUpdate();
		} finally {
			try {
				if (preparedStatement != null)
					 preparedStatement.close();
			} finally {
				connection.close();
			}
		}
		
		
	}

	@Override
	public synchronized boolean doDelete(int code) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		int result = 0;
		
		String deleteSQL = "DELETE FROM " + InfoDaoDataSource.TABLE_NAME + " WHERE CODE = ?";
		
		try {
			connection= ds.getConnection();
			preparedStatement = connection.prepareStatement(deleteSQL);
			preparedStatement.setInt(1, code);
			
			result = preparedStatement.executeUpdate();
			
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
	public InfoBean doRetrieveByKey(int code) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		InfoBean bean= new InfoBean();
		String selectSQL = "SELECT * FROM " + InfoDaoDataSource.TABLE_NAME + " WHERE CODE= ? ";
		
		try {
			//if(ds==null) System.out.println("ds nulla.");
			connection = ds.getConnection();
			//if(connection==null) System.out.println("connesione nulla.");
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setInt(1, code);
			
			ResultSet rs = preparedStatement.executeQuery();
			
			while(rs.next()) {
				bean.setCodice(rs.getInt("CODE"));
				bean.setNome(rs.getString("NAME"));
				bean.setCosto(rs.getDouble("PRICE"));
				bean.setDescrizione(rs.getString("DESCRIPTION"));
				bean.setDisponibilità(rs.getInt("AVAILABILITY"));	
				bean.setTipologia(rs.getString("TYPE"));	
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		
		return bean;
	}
	@Override
	public InfoBean doRetrieveByName(String name) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		InfoBean bean= new InfoBean();
		String selectSQL = "SELECT * FROM " + InfoDaoDataSource.TABLE_NAME + " WHERE NAME= ? ";
		
		try {
			//if(ds==null) System.out.println("ds nulla.");
			connection = ds.getConnection();
			//if(connection==null) System.out.println("connesione nulla.");
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setString(1, name);
			
			ResultSet rs = preparedStatement.executeQuery();
			
			while(rs.next()) {
				bean.setCodice(rs.getInt("CODE"));
				bean.setNome(rs.getString("NAME"));
				bean.setCosto(rs.getDouble("PRICE"));
				bean.setDescrizione(rs.getString("DESCRIPTION"));
				bean.setDisponibilità(rs.getInt("AVAILABILITY"));
				bean.setTipologia(rs.getString("TYPE"));
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		
		return bean;
	}
	
	@Override
	public Collection<InfoBean> doRetrieveAll(String order) throws SQLException {
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		Collection<InfoBean> infos= new LinkedList<InfoBean>();
		String selectSQL = "SELECT * FROM " + InfoDaoDataSource.TABLE_NAME;
		
		if(order != null && !order.equals("")) {
			selectSQL +=" ORDER BY " + order;
		}
		
		try {
			connection = ds.getConnection();
			preparedStatement = connection.prepareStatement(selectSQL);
			
			ResultSet rs = preparedStatement.executeQuery();
			
			while(rs.next()) {
				InfoBean bean = new InfoBean();
				
				bean.setCodice(rs.getInt("CODE"));
				bean.setNome(rs.getString("NAME"));
				bean.setCosto(rs.getDouble("PRICE"));
				bean.setDescrizione(rs.getString("DESCRIPTION"));
				bean.setDisponibilità(rs.getInt("AVAILABILITY"));
				bean.setTipologia(rs.getString("TYPE"));
				infos.add(bean);
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		
		return infos;
	}

	@Override
	public void doUpdateQuantity(int code, int quantity) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		String insertSQL="UPDATE " + InfoDaoDataSource.TABLE_NAME 
				+ " SET AVAILABILITY = ? WHERE CODE= ? ";
		
		try {
			connection = ds.getConnection();
			preparedStatement = connection.prepareStatement(insertSQL);
			preparedStatement.setInt(1, quantity);
			preparedStatement.setInt(2, code);
			
			preparedStatement.executeUpdate();
		} finally {
			try {
				if (preparedStatement != null)
					 preparedStatement.close();
			} finally {
				connection.close();
			}
		}
		
		
	}
}
