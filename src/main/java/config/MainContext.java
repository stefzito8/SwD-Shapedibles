package config;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NamingException;
import javax.servlet.ServletContext;
import javax.servlet.ServletContextEvent;
import javax.servlet.ServletContextListener;
import javax.servlet.annotation.WebListener;
import javax.sql.DataSource;
import org.apache.tomcat.dbcp.dbcp2.BasicDataSource;

@WebListener
public class MainContext implements ServletContextListener 
{
	public void contextInitialized(ServletContextEvent sce) {
		ServletContext context = sce.getServletContext();
		String dbPath = sce.getServletContext().getRealPath("/WEB-INF/dbshape.db");
		//Per usare il Data  Source
		DataSource ds = null; 
		try	{
			Context initCtx = new InitialContext();
			Context envCtx = (Context) initCtx.lookup("java:comp/env");

			ds = (DataSource) envCtx.lookup("db/dbshape");

			if (ds instanceof BasicDataSource) {
            BasicDataSource bds = (BasicDataSource) ds;
            
            // Imposta l'URL con il percorso dinamico calcolato
            bds.setUrl("jdbc:sqlite:" + dbPath); 
        }

		} catch (NamingException e) {
			System.out.println("Error:" + e.getMessage());
		}
		

		context.setAttribute("DataSource", ds);
		System.out.println("DataSource creation...."+ds.toString());

		try {
			Class.forName("com.mysql.cj.jdbc.Driver");
		} catch (ClassNotFoundException e) {
			System.err.println("MySQL JDBC Driver not found: " + e.getMessage());
		}
	}

	public void contextDestroyed(ServletContextEvent sce) {
	}
}
