package model.bean;

import java.io.Serializable;

public class AddressBean implements Serializable{

	private static final long serialVersionUID = 1L;
	
	private /*@ spec_public @*/ String id;
	private /*@ spec_public @*/ String utente;
	private /*@ spec_public @*/ String paese;
	private /*@ spec_public @*/ String strada;
	private /*@ spec_public @*/ String città;
	private /*@ spec_public @*/ int numero;
	private /*@ spec_public @*/ String codice_postale;
	
	//@ pure 
	public String getId()
	{
		return id;
	}
	
	//@ pure 
	public String getUtente()
	{
		return utente;
	}
	
	//@ pure 
	public String getPaese()
	{
		return paese;
	}
	
	//@ pure 
	public String getStrada()
	{
		return strada;
	}

	//@ pure 
	public String getCittà()
	{
		return città;
	}
	
	//@ pure 
	public int getNumero()
	{
		return numero;
	}
	
	//@ pure 
	public String getCodicePostale()
	{
		return codice_postale;
	}
	//@ assignable this.id; 
	public void setId(String id)
	{
		this.id=id;
	}
	
	//@ assignable this.utente; 
	public void setUtente(String utente)
	{
		this.utente=utente;
	}
	
	//@ assignable this.paese; 
	public void setPaese(String paese)
	{
		this.paese=paese;
	}
	
	//@ assignable this.strada; 
	public void setStrada(String strada)
	{
		this.strada=strada;
	}
	
	//@ assignable this.città; 	
	public void setCittà(String città)
	{
		this.città=città;
	}
	
	//@ assignable this.numero; 
	public void setNumero(int numero)
	{
		this.numero=numero;
	}
	
	//@ assignable this.codice_postale; 
	public void setCodicePostale(String codice_postale)
	{
		this.codice_postale=codice_postale;
	}
	
	//@  pure
	@Override
	public String toString() {
		return id + " " + utente + " " + paese + " " + strada + " "+ città + " " + numero + " " + codice_postale;
	}

	//@  pure
	public String selectString() {
		return paese + ", " + strada + ", "+ città + ", " + numero + ", " + codice_postale;
	}
	
	
}

