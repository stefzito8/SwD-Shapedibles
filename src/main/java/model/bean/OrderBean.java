package model.bean;

import java.io.Serializable;

public class OrderBean implements Serializable{

	private static final long serialVersionUID = 1L;
	
	private /*@ spec_public @*/ String utente;
	private /*@ spec_public @*/ int codice;
	private /*@ spec_public @*/ String indirizzo;
	private /*@ spec_public @*/ String stato;
	private /*@ spec_public @*/ String data_ordine;
	private /*@ spec_public @*/ double saldo_totale;
	
	public OrderBean()
	{
	  utente=" ";
	  codice=0;
	  indirizzo=" ";
	  stato=" ";
	  data_ordine=" ";
	  saldo_totale=0.0;
	}
	
	//@ pure
	public String getUtente()
	{ 
		return utente;
	}
	
	//@ pure
	public int getCodice()
	{ 
		return codice;
	}
	
	//@ pure
	public String getIndirizzo()
	{ 
		return indirizzo;
	}

	//@ pure
	public String getStato()
	{ 
		return stato;
	}

	//@ pure
	public String getDataOrdine()
	{ 
		return data_ordine;
	}
	
	//@ pure
	public double getSaldoTotale()
	{ 
		return saldo_totale;
	}
	
	//@ assignable this.utente; 
	public void setUtente(String utente) 
	{
	  this.utente=utente;	
	}
	
	//@ assignable this.codice; 
	public void setCodice(int codice) 
	{
	  this.codice=codice;
	}
	
	//@ assignable this.indirizzo; 
	public void setIndirizzo(String indirizzo) 
	{
	  this.indirizzo=indirizzo;
	}
	
	//@ assignable this.stato; 	
	public void setStato(String stato) 
	{
	  this.stato=stato;
	}
	
	//@ assignable this.data_ordine; 
	public void setDataOrdine(String data_ordine)
	{
	  this.data_ordine=data_ordine;	
	}
	
	//@ assignable this.saldo_totale; 
	public void setSaldoTotale(double saldo_totale) 
	{
	  this.saldo_totale=saldo_totale;
	}
	
	//@  pure
	@Override
	public String toString() {
		return utente + " (" + codice + "), " + indirizzo + " " + stato + " "+ data_ordine + " " + saldo_totale;
	}
	
}

