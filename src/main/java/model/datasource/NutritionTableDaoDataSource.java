package model.datasource;


import model.bean.NutritionTableBean;
import model.dao.INutritionTableDao;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Collection;
import java.util.LinkedList;

public class NutritionTableDaoDataSource implements INutritionTableDao
{
	private static final String TABLE_NAME="nutritionalValues";
	private DataSource ds=null;
	
	public NutritionTableDaoDataSource(DataSource ds)
	{
		this.ds=ds;
		System.out.println("DriverManager Product Model creation....");
	}
	
	@Override
	public void doSave(NutritionTableBean nutritionTable) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		String insertSQL="INSERT INTO " + NutritionTableDaoDataSource.TABLE_NAME 
				+ " (Product_Code, energy, fats, saturated_fats, carbs, sugars, fibers, proteins, salt) VALUES (?,?,?,?,?,?,?,?,?)";
		
		try {
			connection = ds.getConnection();
			preparedStatement = connection.prepareStatement(insertSQL);
			preparedStatement.setInt(1, nutritionTable.getCodiceProdotto());
			preparedStatement.setInt(2, nutritionTable.getEnergia());
			preparedStatement.setDouble(3, nutritionTable.getGrassi());
			preparedStatement.setDouble(4, nutritionTable.getGrassiSaturi());
			preparedStatement.setDouble(5, nutritionTable.getCarboedrati());
			preparedStatement.setDouble(6, nutritionTable.getZucherri());
			preparedStatement.setDouble(7, nutritionTable.getFibre());
			preparedStatement.setDouble(8, nutritionTable.getProteine());
			preparedStatement.setDouble(9, nutritionTable.getSale());
			
			preparedStatement.executeUpdate();
		} 
		finally {
			try {
				if (preparedStatement != null)
					 preparedStatement.close();
			} finally {
				connection.close();
			}
		}
	}

	@Override
	public boolean doDelete(int productID) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		int result = 0;
		
		String deleteSQL = "DELETE FROM " + NutritionTableDaoDataSource.TABLE_NAME + " WHERE PRODUCT_CODE = ?";
		
		try {
			connection= ds.getConnection();
			preparedStatement = connection.prepareStatement(deleteSQL);
			preparedStatement.setInt(1, productID);
			
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
	public NutritionTableBean doRetrieveByKey(int productID) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		NutritionTableBean bean= new NutritionTableBean();
		String selectSQL = "SELECT * FROM " + NutritionTableDaoDataSource.TABLE_NAME + " WHERE PRODUCT_CODE = ?";
		
		try {
			connection = ds.getConnection();
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setInt(1, productID);
			
			ResultSet rs = preparedStatement.executeQuery();
			
			while(rs.next()) {
				bean.setCodiceProdotto(rs.getInt("PRODUCT_CODE"));
				bean.setEnergia(rs.getInt("ENERGY"));
				bean.setGrassi(rs.getInt("FATS"));
				bean.setGrassiSaturi(rs.getInt("SATURATED_FATS"));
				bean.setCarboedrati(rs.getInt("CARBS"));
				bean.setZucherri(rs.getInt("SUGARS"));
				bean.setFibre(rs.getInt("FIBERS"));
				bean.setProteine(rs.getInt("PROTEINS"));
				bean.setSale(rs.getInt("SALT"));
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
	public Collection<NutritionTableBean> doRetrieveAll(String order) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		Collection<NutritionTableBean> tables= new LinkedList<NutritionTableBean>();
		String selectSQL = "SELECT * FROM " + NutritionTableDaoDataSource.TABLE_NAME;
		
		if(order != null && !order.equals("")) {
			selectSQL +=" ORDER BY " + order;
		}
		
		try {
			connection = ds.getConnection();
			preparedStatement = connection.prepareStatement(selectSQL);
			
			ResultSet rs = preparedStatement.executeQuery();
			
			while(rs.next()) {
				NutritionTableBean  bean = new NutritionTableBean();
				
				bean.setCodiceProdotto(rs.getInt("PRODUCT_CODE"));
				bean.setEnergia(rs.getInt("ENERGY"));
				bean.setGrassi(rs.getInt("FATS"));
				bean.setGrassiSaturi(rs.getInt("SATURATED_FATS"));
				bean.setCarboedrati(rs.getInt("CARBS"));
				bean.setZucherri(rs.getInt("SUGARS"));
				bean.setFibre(rs.getInt("FIBERS"));
				bean.setProteine(rs.getInt("PROTEINS"));
				bean.setSale(rs.getInt("SALT"));
				tables.add(bean);
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		
		return tables;
	}

}
