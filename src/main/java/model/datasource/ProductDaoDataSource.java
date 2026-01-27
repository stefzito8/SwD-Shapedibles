package model.datasource;

import model.bean.ProductBean;
import model.dao.IProductDao;

import javax.sql.DataSource;
import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;


public class ProductDaoDataSource implements IProductDao
{
	private static final String TABLE_NAME = "product";

	//@ spec_public non_null
	private DataSource ds;
	
	//@ public invariant ds != null;

	//@ requires ds != null;
	//@ ensures this.ds == ds;
	public ProductDaoDataSource(DataSource ds)
	{
		this.ds=ds;
		System.out.println("DriverManager Product Model creation....");
	}
	
	@Override
	public void doSave(ProductBean product) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		String insertSQL="INSERT INTO " + ProductDaoDataSource.TABLE_NAME 
				+ " (current_infos, name) VALUES (?,?)";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(insertSQL);
			preparedStatement.setInt(1, product.getInfoCorrenti());
			preparedStatement.setString(2, product.getNome());
			
			
			preparedStatement.executeUpdate();
		} finally {
    try {
        if (preparedStatement != null)
            preparedStatement.close();
    } catch (SQLException e) {
        e.printStackTrace();
    }
    
    // CORREZIONE QUI:
    try {
        if (connection != null) {
            connection.close();
        }
    } catch (SQLException e) {
        e.printStackTrace();
    }
}
		
		
	}

	@Override
	public synchronized boolean doDelete(int code) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		int result;
		
		String deleteSQL = "DELETE FROM " + ProductDaoDataSource.TABLE_NAME + " WHERE CODE = ?";
		
		try {
			connection= ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(deleteSQL);
			preparedStatement.setInt(1, code);
			
			result = preparedStatement.executeUpdate();
			//@ assert result >= 0;
		} finally {
    try {
        if (preparedStatement != null)
            preparedStatement.close();
    } catch (SQLException e) {
        e.printStackTrace();
    }
    
    // CORREZIONE QUI:
    try {
        if (connection != null) {
            connection.close();
        }
    } catch (SQLException e) {
        e.printStackTrace();
    }
}
		return (result!=0);
	}

	@Override
	public ProductBean doRetrieveByKey(int code) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		/*@ nullable @*/ImageDaoDataSource imageDaoDataSource = new ImageDaoDataSource(ds);
		
		ProductBean bean= new ProductBean();
		//@ assert bean != null;
		String selectSQL = "SELECT * FROM " + ProductDaoDataSource.TABLE_NAME + " WHERE CODE= ? ";
		
		try {

			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setInt(1, code);
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;
			while(rs.next()) {
				bean.setCodice(rs.getInt("CODE"));
				bean.setNome(rs.getString("NAME"));
				bean.setInfoCorrenti(rs.getInt("CURRENT_INFOS"));
				//@assume bean.getCodice() != 0;
				bean.setImages(imageDaoDataSource.doRetrieveByProduct(bean.getCodice()));
			}
			
		} finally {
    try {
        if (preparedStatement != null)
            preparedStatement.close();
    } catch (SQLException e) {
        e.printStackTrace();
    }
    
    // CORREZIONE QUI:
    try {
        if (connection != null) {
            connection.close();
        }
    } catch (SQLException e) {
        e.printStackTrace();
    }
}
		//@ assert bean != null;
		return bean;
	}


	@Override
	public ProductBean doRetrieveByName(String name) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		/*@ nullable @*/ImageDaoDataSource imageDaoDataSource = new ImageDaoDataSource(ds);
		
		ProductBean bean= new ProductBean();
		//@ assert bean != null;
		String selectSQL = "SELECT * FROM " + ProductDaoDataSource.TABLE_NAME + " WHERE NAME= ? ";
		
		try {

			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setString(1, name);
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;

			while(rs.next()) {
				bean.setCodice(rs.getInt("CODE"));
				bean.setNome(rs.getString("NAME"));
				bean.setInfoCorrenti(rs.getInt("CURRENT_INFOS"));
				//@assume bean.getCodice() != 0;
				bean.setImages(imageDaoDataSource.doRetrieveByProduct(bean.getCodice()));
			}
			
		} finally {
    try {
        if (preparedStatement != null)
            preparedStatement.close();
    } catch (SQLException e) {
        e.printStackTrace();
    }
    
    // CORREZIONE QUI:
    try {
        if (connection != null) {
            connection.close();
        }
    } catch (SQLException e) {
        e.printStackTrace();
    }
}
		
		return bean;
	}
	
	@Override
	public Collection<ProductBean> doRetrieveAll(String order) throws SQLException {
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		/*@ nullable @*/ImageDaoDataSource imageDaoDataSource = new ImageDaoDataSource(ds);
		
		Collection<ProductBean> products= new LinkedList<>();
		//@ assert products != null && products.isEmpty();

		String selectSQL = "SELECT * FROM " + ProductDaoDataSource.TABLE_NAME;
		
		if(order != null && !order.isEmpty()) {
			selectSQL +=" ORDER BY " + order;
		}
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;
			
			/*@ 
              @ loop_invariant products != null;
              @*/
			while(rs.next()) {
				ProductBean bean = new ProductBean();
				
				bean.setCodice(rs.getInt("CODE"));
				bean.setNome(rs.getString("NAME"));
				bean.setInfoCorrenti(rs.getInt("CURRENT_INFOS"));	
				//@ assume bean.getCodice() >= 0;
				bean.setImages(imageDaoDataSource.doRetrieveByProduct(bean.getCodice()));
				
				//@ assert bean != null;
				products.add(bean);
				//@ assert !products.isEmpty();
			}
			
		} finally {
    try {
        if (preparedStatement != null)
            preparedStatement.close();
    } catch (SQLException e) {
        e.printStackTrace();
    }
    
    // CORREZIONE QUI:
    try {
        if (connection != null) {
            connection.close();
        }
    } catch (SQLException e) {
        e.printStackTrace();
    }
}
		
		return products;
	}
	

	@Override
	public List<ProductBean> searchByName(String query) throws SQLException {
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		/*@ nullable @*/ImageDaoDataSource imageDaoDataSource = new ImageDaoDataSource(ds);
		
		List<ProductBean> products = new LinkedList<>();
		//@ assert products != null && products.isEmpty();
		String selectSQL = "SELECT * FROM " + ProductDaoDataSource.TABLE_NAME + " WHERE NAME LIKE ?";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(selectSQL);
			preparedStatement.setString(1, "%" + query + "%");
			
			ResultSet rs = preparedStatement.executeQuery();
			//@ assert rs != null;

			/*@ 
              @ loop_invariant products != null;
              @*/
			while(rs.next()) {
				ProductBean bean = new ProductBean();
				
				bean.setCodice(rs.getInt("CODE"));
				bean.setNome(rs.getString("NAME"));
				bean.setInfoCorrenti(rs.getInt("CURRENT_INFOS"));
				bean.setImages(imageDaoDataSource.doRetrieveByProduct(bean.getCodice()));
				//@ assert bean != null;
				products.add(bean);
				//@ assert !products.isEmpty();
			}
			
		} finally {
    try {
        if (preparedStatement != null)
            preparedStatement.close();
    } catch (SQLException e) {
        e.printStackTrace();
    }
    
    // CORREZIONE QUI:
    try {
        if (connection != null) {
            connection.close();
        }
    } catch (SQLException e) {
        e.printStackTrace();
    }
}
		
		return products;
	}

	@Override
	public void doUpdateInfo(int code, int codiceInfo) throws SQLException {
		// TODO Auto-generated method stub
		/*@ nullable @*/Connection connection = null;
		/*@ nullable @*/PreparedStatement preparedStatement = null;
		
		String insertSQL="UPDATE " + ProductDaoDataSource.TABLE_NAME 
				+ " SET CURRENT_INFOS = ? WHERE CODE= ? ";
		
		try {
			connection = ds.getConnection();
			//@ assert connection != null;
			preparedStatement = connection.prepareStatement(insertSQL);
			preparedStatement.setInt(1, codiceInfo);
			preparedStatement.setInt(2, code);
			
			preparedStatement.executeUpdate();
		} finally {
    try {
        if (preparedStatement != null)
            preparedStatement.close();
    } catch (SQLException e) {
        e.printStackTrace();
    }
    
    // CORREZIONE QUI:
    try {
        if (connection != null) {
            connection.close();
        }
    } catch (SQLException e) {
        e.printStackTrace();
    }
}
		
	}

}
