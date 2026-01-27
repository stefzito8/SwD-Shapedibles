package model.datasource;

import model.bean.AddressBean;
import model.dao.IAddressDao;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Collection;
import java.util.LinkedList;

public class AddressDaoDataSource implements IAddressDao
{
	private static final String TABLE_NAME="adresses";
	
	//@ spec_public non_null
	private DataSource ds;
	
	//@ public invariant ds != null;

	//@ requires ds != null;
	//@ ensures this.ds == ds;
	public AddressDaoDataSource(DataSource ds)
	{
		this.ds=ds;
		System.out.println("DriverManager address Model creation....");
	}

	@Override
	public void doSave(AddressBean coupon) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		String insertSQL="INSERT INTO " + AddressDaoDataSource.TABLE_NAME 
				+ " (id, \"user\", country, street, city, number, Postal_Code) VALUES (?,?,?,?,?,?,?)";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(insertSQL);
			preparedStatement.setString(1, coupon.getId());
			preparedStatement.setString(2, coupon.getUtente());
			preparedStatement.setString(3, coupon.getPaese());
			preparedStatement.setString(4, coupon.getStrada());
			preparedStatement.setString(5, coupon.getCittà());
			preparedStatement.setInt(6, coupon.getNumero());
			preparedStatement.setString(7, coupon.getCodicePostale());
			
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
	public boolean doDelete(String id, String user) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		int result = 0;
		
		String deleteSQL = "DELETE FROM " + AddressDaoDataSource.TABLE_NAME + " WHERE ID = ? AND \"user\"= ? ";
		
		try {
			connection= ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(deleteSQL);
			preparedStatement.setString(1, id);
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
	public AddressBean doRetrieveByKey(String id, String user) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		AddressBean bean= new AddressBean();
		//@ assert bean != null;
		String selectSQL = "SELECT * FROM " + AddressDaoDataSource.TABLE_NAME + " WHERE ID = ?  AND \"user\"= ? ";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setString(1, id);
			preparedStatement.setString(2, user);
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;
			while(rs.next()) {
				bean.setId(rs.getString("ID"));
				bean.setUtente(rs.getString("user"));
				bean.setPaese(rs.getString("country"));
				bean.setStrada(rs.getString("street"));
				bean.setCittà(rs.getString("city"));
				bean.setNumero(rs.getInt("number"));
				bean.setCodicePostale(rs.getString("Postal_Code"));
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
	public Collection<AddressBean> doRetrieveAll(String order) throws SQLException {
		// TODO Auto-generated method stub
				/*@ nullable @*/Connection connection = null;
				/*@ nullable @*/PreparedStatement preparedStatement = null;
				
				Collection<AddressBean> Addresses= new LinkedList<AddressBean>();
				//@ assert Addresses != null && Addresses.isEmpty();
				String selectSQL = "SELECT * FROM " + AddressDaoDataSource.TABLE_NAME;
				
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
			  		@ loop_invariant Addresses != null;
			  		@*/
					while(rs.next()) {
						AddressBean  bean = new AddressBean();
						
						bean.setId(rs.getString("ID"));
						bean.setUtente(rs.getString("user"));
						bean.setPaese(rs.getString("country"));
						bean.setStrada(rs.getString("street"));
						bean.setCittà(rs.getString("city"));
						bean.setNumero(rs.getInt("number"));
						bean.setCodicePostale(rs.getString("Postal_Code"));
						//@ assert bean != null;
						Addresses.add(bean);
						//@ assert !Addresses.isEmpty();
					}
					
				} finally {
					try{
						if(preparedStatement != null)
							preparedStatement.close();
				} finally{
					connection.close();
				}
				}
				
				return Addresses;
				}

	@Override
	public Collection<AddressBean> doRetrieveByUser(String user) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		Collection<AddressBean> Addresses= new LinkedList<AddressBean>();
		//@ assert Addresses != null && Addresses.isEmpty();
		String selectSQL = "SELECT * FROM " + AddressDaoDataSource.TABLE_NAME + " WHERE \"user\"= ? ";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setString(1, user);
			ResultSet rs = preparedStatement.executeQuery();
			
			//@ assert rs != null;
			/*@ 
			  @ loop_invariant Addresses != null;
			  @*/
			while(rs.next()) {
				AddressBean  bean = new AddressBean();
				
				bean.setId(rs.getString("ID"));
				bean.setUtente(rs.getString("user"));
				bean.setPaese(rs.getString("country"));
				bean.setStrada(rs.getString("street"));
				bean.setCittà(rs.getString("city"));
				bean.setNumero(rs.getInt("number"));
				bean.setCodicePostale(rs.getString("Postal_Code"));
				//@ assert bean != null;
				Addresses.add(bean);
				//@ assert !Addresses.isEmpty();
			}
			
		} finally {
			try{
				if(preparedStatement != null)
					preparedStatement.close();
		} finally{
			connection.close();
		}
		}
		
		return Addresses;
	}
}
