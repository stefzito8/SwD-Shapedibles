package model.datasource;

import model.bean.ImageBean;
import model.dao.IImageDao;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Collection;
import java.util.LinkedList;

public class ImageDaoDataSource implements IImageDao
{
	private static final String TABLE_NAME="images";
	//@ spec_public non_null
	private DataSource ds;
	
	//@ public invariant ds != null;

	//@ requires ds != null;
	//@ ensures this.ds == ds;
	public ImageDaoDataSource(DataSource ds)
	{
		this.ds=ds;
		System.out.println("DriverManager Product Model creation....");
	}
	
	@Override
	public void doSave(ImageBean image) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		String insertSQL="INSERT INTO " + ImageDaoDataSource.TABLE_NAME 
				+ " (img, Product_code) VALUES (?,?)";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(insertSQL);
			preparedStatement.setString(1, image.getImg());
			preparedStatement.setInt(2, image.getCodiceProdotto());
			
			

			
			preparedStatement.executeUpdate();
		} 
		finally {
			try {
				if (preparedStatement != null)
					 preparedStatement.close();
			} finally {
                assert connection != null;
                connection.close();
			}
		}
	}

	@Override
	public boolean doDelete(int num, int codice) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		int result;
		
		String deleteSQL = "DELETE FROM " + ImageDaoDataSource.TABLE_NAME + " WHERE Product_Code = ? AND  Images_Num = ?";
		
		try {
			connection= ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(deleteSQL);
			preparedStatement.setInt(1, codice);
			preparedStatement.setInt(2, num);
			
			result = preparedStatement.executeUpdate();
			//@ assert result >= 0;
		} finally {
			try {
				if (preparedStatement != null)
					preparedStatement.close();
			} finally {
                assert connection != null;
                connection.close();
			}
		}
		return (result!=0);
	}

	@Override
	public ImageBean doRetrieveByKey(int codice, int num) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		ImageBean bean= new ImageBean();
		//@ assert bean != null;
		String selectSQL = "SELECT * FROM " + ImageDaoDataSource.TABLE_NAME + " WHERE Product_Code = ? AND Images_Num = ? ";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setInt(1, codice);
			
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;
			while(rs.next()) {
				bean.setNumImage(rs.getInt("Images_Num"));
				bean.setCodiceProdotto(rs.getInt("Product_Code"));
				bean.setImg(rs.getString("img"));  
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
                assert connection != null;
                connection.close();
		}
		}
		//@ assert bean != null;
		return bean;
	}

	@Override
	public Collection<ImageBean> doRetrieveAll(String order) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		Collection<ImageBean> images= new LinkedList<>();
		//@ assert images != null && images.isEmpty();
		String selectSQL = "SELECT * FROM " + ImageDaoDataSource.TABLE_NAME;
		
		if(order != null && !order.isEmpty()) {
			selectSQL +=" ORDER BY " + order;
		}
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			//@ assert rs != null;
			/*@ 
              @ loop_invariant images != null;
              @*/
			ResultSet rs = preparedStatement.executeQuery();
			
			while(rs.next()) {
				ImageBean  bean = new ImageBean();
				
				bean.setNumImage(rs.getInt("Images_Num"));
				bean.setCodiceProdotto(rs.getInt("Product_Code"));
				bean.setImg(rs.getString("img"));  
				//@ assert bean != null;
				images.add(bean);
				//@ assert !images.isEmpty();
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
                assert connection != null;
                connection.close();
		}
		}
		
		return images;
	}

	@Override
	public Collection<ImageBean> doRetrieveByProduct(int codice) throws SQLException {
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		Collection<ImageBean> images= new LinkedList<ImageBean>();
		//@ assert images != null && images.isEmpty();
		String selectSQL = "SELECT * FROM " + ImageDaoDataSource.TABLE_NAME + " WHERE Product_Code= ? ";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setInt(1, codice);
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;
			
			/*@ 
              @ loop_invariant images != null;
              @*/
			while(rs.next()) {
				ImageBean  bean = new ImageBean();
				
				bean.setNumImage(rs.getInt("Images_Num"));
				bean.setCodiceProdotto(rs.getInt("Product_Code"));
				bean.setImg(rs.getString("img"));  
				//@ assert bean != null;
				images.add(bean);
				//@ assert !images.isEmpty();
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		
		return images;

	}
}
