package model.datasource;


import model.bean.UserBean;
import model.dao.IUserDao;

import javax.sql.DataSource;
import java.security.NoSuchAlgorithmException;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Collection;
import java.util.LinkedList;

public class UserDaoDataSource implements IUserDao {
	
	private static final String TABLE_NAME="users";
	private DataSource ds=null;
	
	public UserDaoDataSource(DataSource ds)
	{
		this.ds=ds;
		System.out.println("DriverManager Product Model creation....");
	}
	
	@Override
	public void doSave(UserBean user) throws SQLException
	{
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		String insertSQL="INSERT INTO " + UserDaoDataSource.TABLE_NAME 
				+ "(Username, email, pass, name_surname, gender, country, birthday, user_admin) VALUES (?,?,?,?,?,?,?,?)";
		
		try {
			connection = ds.getConnection();
			preparedStatement = connection.prepareStatement(insertSQL);
			preparedStatement.setString(1, user.getUsername());
			preparedStatement.setString(2, user.getEmail());
			preparedStatement.setString(3, user.getPass());
			preparedStatement.setString(4, user.getNomeCognome());
			preparedStatement.setString(5, user.getSesso());
			preparedStatement.setString(6, user.getPaese());
			preparedStatement.setString(7, user.getDataNascita());
			preparedStatement.setInt(8, user.getUserAdmin());
		
			
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
	public boolean doDelete(String username) throws SQLException {
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		int result = 0;
		
		String deleteSQL = "DELETE FROM " +UserDaoDataSource.TABLE_NAME + " WHERE USERNAME = ?";
		
		try {
			connection= ds.getConnection();
			preparedStatement = connection.prepareStatement(deleteSQL);
			preparedStatement.setString(1, username);
			
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
	public UserBean doRetrieveByKey(String username) throws SQLException {
		// TODO Auto-generated method stub
				Connection connection = null;
				PreparedStatement preparedStatement = null;
				
				UserBean bean= new UserBean();
				String selectSQL = "SELECT * FROM " + UserDaoDataSource.TABLE_NAME + " WHERE USERNAME = ?";
				
				try {
					connection = ds.getConnection();
					preparedStatement = connection.prepareStatement(selectSQL);
					preparedStatement.setString(1, username);
					
					ResultSet rs = preparedStatement.executeQuery();
					
					while(rs.next()) {
						bean.setUsername(rs.getString("USERNAME"));
						bean.setEmail(rs.getString("EMAIL"));
						bean.setPass(rs.getString("PASS"));
						bean.setNomeCognome(rs.getString("NAME_SURNAME"));
						bean.setSesso(rs.getString("GENDER"));
						bean.setPaese(rs.getString("COUNTRY"));
						bean.setDataNascita(rs.getString("BIRTHDAY"));
						bean.setUserAdmin(rs.getInt("USER_ADMIN"));
					}
					
				} 
				finally {
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
	public Collection<UserBean> doRetrieveAll(String order) throws SQLException{
		// TODO Auto-generated method stub
		Connection connection = null;
		PreparedStatement preparedStatement = null;
		
		Collection<UserBean> users= new LinkedList<UserBean>();
		String selectSQL = "SELECT * FROM " + UserDaoDataSource.TABLE_NAME;
		
		if(order != null && !order.equals("")) {
			selectSQL +=" ORDER BY" + order;
		}
		
		try {
			connection = ds.getConnection();
			preparedStatement = connection.prepareStatement(selectSQL);
			
			ResultSet rs = preparedStatement.executeQuery();
			
			while(rs.next()) {
				UserBean  bean = new UserBean();
				
				bean.setUsername(rs.getString("USERNAME"));
				bean.setEmail(rs.getString("EMAIL"));
				bean.setPass(rs.getString("PASS"));
				bean.setNomeCognome(rs.getString("NAME_SURNAME"));
				bean.setSesso(rs.getString("GENDER"));
				bean.setPaese(rs.getString("COUNTRY"));
				bean.setDataNascita(rs.getString("BIRTHDAY"));
				bean.setUserAdmin(rs.getInt("USER_ADMIN"));
				users.add(bean);
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		
		return users;
	}
 
}
