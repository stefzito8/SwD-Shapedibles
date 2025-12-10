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
    
    // MODIFICA: spec_public non_null aiuta a prevenire i "NullField" errors
    //@ spec_public non_null
    private DataSource ds;
    
    //@ public invariant ds != null;

    //@ requires ds != null;
    //@ ensures this.ds == ds;
    public InfoDaoDataSource(DataSource ds) {
        this.ds = ds;
        System.out.println("DriverManager info Model creation....");
    }
    
    @Override
    public void doSave(InfoBean info) throws SQLException {
        /*@ nullable @*/ Connection connection = null;
        /*@ nullable @*/ PreparedStatement preparedStatement = null;
        
        String insertSQL = "INSERT INTO product_info (name, price, description, availability , type) VALUES (?,?,?,?,?)";
        
        try {
            connection = ds.getConnection();
            //@ assert connection != null;
            
            preparedStatement = connection.prepareStatement(insertSQL);
            preparedStatement.setString( 1, info.getNome());
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
                if (connection != null)
                    connection.close();
            }
        }
    }

    @Override
    public synchronized boolean doDelete(int code) throws SQLException {
        /*@ nullable @*/ Connection connection = null;
        /*@ nullable @*/ PreparedStatement preparedStatement = null;
        
        int result = 0;
        String deleteSQL = "DELETE FROM product_info WHERE CODE = ?";
        
        try {
            connection = ds.getConnection();
             //@ assert connection != null;
            preparedStatement = connection.prepareStatement(deleteSQL);
            preparedStatement.setInt(1, code);
            
            result = preparedStatement.executeUpdate();
            //@ assert result >= 0;
            
        } finally {
            try {
                if (preparedStatement != null)
                    preparedStatement.close();
            } finally {
                if (connection != null)
                    connection.close();
            }
        }
        return (result != 0);
    }

    @Override
    public InfoBean doRetrieveByKey(int code) throws SQLException {
        /*@ nullable @*/ Connection connection = null;
        /*@ nullable @*/ PreparedStatement preparedStatement = null;
        
        InfoBean bean = new InfoBean();
        //@ assert bean != null;
        String selectSQL = "SELECT * FROM product_info WHERE CODE= ? ";
        
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
                bean.setCosto(rs.getDouble("PRICE"));
                bean.setDescrizione(rs.getString("DESCRIPTION"));
                bean.setDisponibilità(rs.getInt("AVAILABILITY"));   
                bean.setTipologia(rs.getString("TYPE"));    
            }
        } finally {
            try {
                if(preparedStatement != null) preparedStatement.close();
            } finally {
                if (connection != null) connection.close();
            }
        }
        return bean;
    }

    @Override
    public InfoBean doRetrieveByName(String name) throws SQLException {
        /*@ nullable @*/ Connection connection = null;
        /*@ nullable @*/ PreparedStatement preparedStatement = null;
        
        InfoBean bean = new InfoBean();
        //@ assert bean != null;
        String selectSQL = "SELECT * FROM product_info WHERE NAME= ? ";
        
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
                bean.setCosto(rs.getDouble("PRICE"));
                bean.setDescrizione(rs.getString("DESCRIPTION"));
                bean.setDisponibilità(rs.getInt("AVAILABILITY"));
                bean.setTipologia(rs.getString("TYPE"));
            }
        } finally {
            try {
                if(preparedStatement != null) preparedStatement.close();
            } finally {
                if (connection != null) connection.close();
            }
        }
        return bean;
    }
    
    @Override
    public Collection<InfoBean> doRetrieveAll(String order) throws SQLException {
        /*@ nullable @*/ Connection connection = null;
        /*@ nullable @*/ PreparedStatement preparedStatement = null;
        
        Collection<InfoBean> infos = new LinkedList<InfoBean>();
        //@ assert infos != null && infos.isEmpty();
        String selectSQL = "SELECT * FROM product_info";
        
        if(order != null && !order.equals("")) {
            selectSQL +=" ORDER BY " + order;
        }
        
        try {
            connection = ds.getConnection();
            //@ assert connection != null;
            preparedStatement = connection.prepareStatement(selectSQL);
            
            ResultSet rs = preparedStatement.executeQuery();
            //@ assert rs != null;
            /*@ loop_invariant infos != null; @*/
            while(rs.next()) {
                InfoBean bean = new InfoBean();
                bean.setCodice(rs.getInt("CODE"));
                bean.setNome(rs.getString("NAME"));
                bean.setCosto(rs.getDouble("PRICE"));
                bean.setDescrizione(rs.getString("DESCRIPTION"));
                bean.setDisponibilità(rs.getInt("AVAILABILITY"));
                bean.setTipologia(rs.getString("TYPE"));
                //@ assert bean != null;
                infos.add(bean);
                //@ assert !infos.isEmpty();
            }
        } finally {
            try {
                if(preparedStatement != null) preparedStatement.close();
            } finally {
                if (connection != null) connection.close();
            }
        }
        return infos;
    }

    @Override
    public void doUpdateQuantity(int code, int quantity) throws SQLException {
        /*@ nullable @*/ Connection connection = null;
        /*@ nullable @*/ PreparedStatement preparedStatement = null;
        
        String insertSQL = "UPDATE product_info SET AVAILABILITY = ? WHERE CODE= ? ";
        
        try {
            connection = ds.getConnection();
            //@ assert connection != null;
            preparedStatement = connection.prepareStatement(insertSQL);
            preparedStatement.setInt(1, quantity);
            preparedStatement.setInt(2, code);
            
            preparedStatement.executeUpdate();
        } finally {
            try {
                if (preparedStatement != null)
                     preparedStatement.close();
            } finally {
                if (connection != null)
                    connection.close();
            }
        }
    }
}