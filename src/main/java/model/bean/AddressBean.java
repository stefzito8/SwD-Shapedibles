package model.bean;

import java.io.Serializable;

public class AddressBean implements Serializable{

	private static final long serialVersionUID = 1L;
	
	String id;
	String utente;
	String paese;
	String strada;
	String città;
	int numero;
	String codice_postale;
	
	public String getId()
	{
		return id;
	}
	
	public String getUtente()
	{
		return utente;
	}
	
	public String getPaese()
	{
		return paese;
	}
	
	public String getStrada()
	{
		return strada;
	}
	
	public String getCittà()
	{
		return città;
	}
	
	public int getNumero()
	{
		return numero;
	}
	
	public String getCodicePostale()
	{
		return codice_postale;
	}
	
	public void setId(String id)
	{
		this.id=id;
	}
	
	public void setUtente(String utente)
	{
		this.utente=utente;
	}
	
	public void setPaese(String paese)
	{
		this.paese=paese;
	}
	
	public void setStrada(String strada)
	{
		this.strada=strada;
	}
	
	public void setCittà(String città)
	{
		this.città=città;
	}
	
	public void setNumero(int numero)
	{
		this.numero=numero;
	}
	
	public void setCodicePostale(String codice_postale)
	{
		this.codice_postale=codice_postale;
	}
	
	@Override
	public String toString() {
		return id + " " + utente + " " + paese + " " + strada + " "+ città + " " + numero + " " + codice_postale;
	}
	

	public String selectString() {
		return paese + ", " + strada + ", "+ città + ", " + numero + ", " + codice_postale;
	}
	
	
}

