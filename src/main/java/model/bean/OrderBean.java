package model.bean;

import java.io.Serializable;

public class OrderBean implements Serializable{

	private static final long serialVersionUID = 1L;
	
	String utente;
	int codice;
	String indirizzo;
	String stato;
	String data_ordine;
	double saldo_totale;
	
	public OrderBean()
	{
	  utente=" ";
	  codice=0;
	  indirizzo=" ";
	  stato=" ";
	  data_ordine=" ";
	  saldo_totale=0.0;
	}
	
	public String getUtente()
	{ 
		return utente;
	}
	
	public int getCodice()
	{ 
		return codice;
	}
	
	public String getIndirizzo()
	{ 
		return indirizzo;
	}
	
	public String getStato()
	{ 
		return stato;
	}
	
	public String getDataOrdine()
	{ 
		return data_ordine;
	}
	
	public double getSaldoTotale()
	{ 
		return saldo_totale;
	}
	
	public void setUtente(String utente) 
	{
	  this.utente=utente;	
	}
	
	public void setCodice(int codice) 
	{
	  this.codice=codice;
	}
	
	public void setIndirizzo(String indirizzo) 
	{
	  this.indirizzo=indirizzo;
	}
	
	public void setStato(String stato) 
	{
	  this.stato=stato;
	}
	
	public void setDataOrdine(String data_ordine)
	{
	  this.data_ordine=data_ordine;	
	}
	
	public void setSaldoTotale(double saldo_totale) 
	{
	  this.saldo_totale=saldo_totale;
	}
	
	@Override
	public String toString() {
		return utente + " (" + codice + "), " + indirizzo + " " + stato + " "+ data_ordine + " " + saldo_totale;
	}
	
}

