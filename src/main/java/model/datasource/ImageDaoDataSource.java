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
	private final DataSource ds;
	
	public ImageDaoDataSource(DataSource ds)
	{
		this.ds=ds;
		System.out.println("DriverManager Product Model creation....");
	}
	
	@Override
	public void doSave(ImageBean image) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		String insertSQL="INSERT INTO " + ImageDaoDataSource.TABLE_NAME 
				+ " (img, Product_code) VALUES (?,?)";
		
		try {
			connection = ds.getConnection();
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
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		int result;
		
		String deleteSQL = "DELETE FROM " + ImageDaoDataSource.TABLE_NAME + " WHERE Product_Code = ? AND  Images_Num = ?";
		
		try {
			connection= ds.getConnection();
			preparedStatement = connection.prepareStatement(deleteSQL);
			preparedStatement.setInt(1, codice);
			preparedStatement.setInt(2, num);
			
			result = preparedStatement.executeUpdate();
			
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
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		ImageBean bean= new ImageBean();
		String selectSQL = "SELECT * FROM " + ImageDaoDataSource.TABLE_NAME + " WHERE Product_Code = ? AND Images_Num = ? ";
		
		try {
			connection = ds.getConnection();
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setInt(1, codice);
			
			
			ResultSet rs = preparedStatement.executeQuery();
			
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
		
		return bean;
	}

	@Override
	public Collection<ImageBean> doRetrieveAll(String order) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		Collection<ImageBean> images= new LinkedList<>();
		String selectSQL = "SELECT * FROM " + ImageDaoDataSource.TABLE_NAME;
		
		if(order != null && !order.isEmpty()) {
			selectSQL +=" ORDER BY" + order;
		}
		
		try {
			connection = ds.getConnection();
			preparedStatement = connection.prepareStatement(selectSQL);
			
			ResultSet rs = preparedStatement.executeQuery();
			
			while(rs.next()) {
				ImageBean  bean = new ImageBean();
				
				bean.setNumImage(rs.getInt("Images_Num"));
				bean.setCodiceProdotto(rs.getInt("Product_Code"));
				bean.setImg(rs.getString("img"));  
				images.add(bean);
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
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		Collection<ImageBean> images= new LinkedList<ImageBean>();
		String selectSQL = "SELECT * FROM " + ImageDaoDataSource.TABLE_NAME + " WHERE Product_Code= ? ";
		
		try {
			connection = ds.getConnection();
			
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setInt(1, codice);
			ResultSet rs = preparedStatement.executeQuery();
			
			while(rs.next()) {
				ImageBean  bean = new ImageBean();
				
				bean.setNumImage(rs.getInt("Images_Num"));
				bean.setCodiceProdotto(rs.getInt("Product_Code"));
				bean.setImg(rs.getString("img"));  
				images.add(bean);
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
