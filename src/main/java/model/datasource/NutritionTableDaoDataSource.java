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
	
	//@ spec_public non_null
	private DataSource ds;
	
	//@ public invariant ds != null;

	//@ requires ds != null;
	//@ ensures this.ds == ds;
	public NutritionTableDaoDataSource(DataSource ds)
	{
		this.ds=ds;
		System.out.println("DriverManager Product Model creation....");
	}
	
	@Override
	public void doSave(NutritionTableBean nutritionTable) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		String insertSQL="INSERT INTO " + NutritionTableDaoDataSource.TABLE_NAME 
				+ " (Product_Code, energy, fats, saturated_fats, carbs, sugars, fibers, proteins, salt) VALUES (?,?,?,?,?,?,?,?,?)";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
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
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		int result = 0;
		
		String deleteSQL = "DELETE FROM " + NutritionTableDaoDataSource.TABLE_NAME + " WHERE PRODUCT_CODE = ?";
		
		try {
			connection= ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(deleteSQL);
			preparedStatement.setInt(1, productID);
			
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
	public NutritionTableBean doRetrieveByKey(int productID) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		NutritionTableBean bean= new NutritionTableBean();
		//@ assert bean != null;
		String selectSQL = "SELECT * FROM " + NutritionTableDaoDataSource.TABLE_NAME + " WHERE PRODUCT_CODE = ?";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setInt(1, productID);
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assume rs != null;
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
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		Collection<NutritionTableBean> tables= new LinkedList<NutritionTableBean>();
		//@ assert tables != null && tables.isEmpty();
		String selectSQL = "SELECT * FROM " + NutritionTableDaoDataSource.TABLE_NAME;
		
		if(order != null && !order.equals("")) {
			selectSQL +=" ORDER BY " + order;
		}
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assume rs != null;

			/*@ 
              @ loop_invariant tables != null;
              @ loop_invariant tables.size() >= 0;
              @*/
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
				//@ assert bean != null;
				tables.add(bean);
				//@ assert !tables.isEmpty();
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
