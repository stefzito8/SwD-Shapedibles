package model.bean;

import java.io.Serializable;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

public class UserBean implements Serializable{

	private static final long serialVersionUID = 1L;
	
	private /*@ spec_public @*/ String username;
	private /*@ spec_public @*/ String email;
	private /*@ spec_public @*/ String pass;
	private /*@ spec_public @*/ String nome_cognome;
	private /*@ spec_public @*/ String sesso;
	private /*@ spec_public @*/ String paese;
	private /*@ spec_public @*/ String data_nascita;
	private /*@ spec_public @*/ int user_admin;
	
	public UserBean()
	{
		username= " ";
		email= " ";
		pass= " ";
		nome_cognome= " ";
		sesso= " ";
		paese= " ";
		data_nascita= " ";
		user_admin= -1;
	}
	
	//@ assignable this.username; 
	public void setUsername(String username) 
	{
		this.username=username;
	}

	//@ assignable this.email;
	public void setEmail(String email) 
	{
		this.email=email;
	}

	//@ assignable this.pass; 
	public void setPass(String pass) 
	{
		this.pass=pass;
	}

	//@ assignable this.nome_cognome; 
	public void setNomeCognome(String nome_cognome) 
	{
		this.nome_cognome=nome_cognome;
	}

	//@ assignable this.sesso; 
	public void setSesso(String sesso) 
	{
		this.sesso=sesso;
	}

	//@ assignable this.paese; 
	public void setPaese(String paese) 
	{
		this.paese=paese;
	}
	
	//@ assignable this.data_nascita; 
	public void setDataNascita(String data_nascita) 
	{
		this.data_nascita=data_nascita;
	}
	
	//@ assignable this.user_admin; 
	public void setUserAdmin(int user_admin) 
	{
		this.user_admin=user_admin;
	}

	//@ pure
	public String getUsername()
	{
		return username;
	}
	
	//@ pure
	public String getEmail()
	{
		return email;
	}
	
	//@ pure
	public String getPass()
	{
		return pass;
	}

	//@ pure
	public String getNomeCognome()
	{
		return nome_cognome;
	}

	//@ pure
	public String getSesso()
	{
		return sesso;
	}

	//@ pure
	public String getPaese()
	{
		return paese;
	}

	//@ pure
	public String getDataNascita()
	{
		return data_nascita;
	}

	//@ pure
	public int getUserAdmin()
	{
		return user_admin;
	}
	
	//@  pure
	@Override
	public String toString() {
		return username + user_admin;
	}

}
