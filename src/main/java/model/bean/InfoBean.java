package model.bean;

import java.io.Serializable;

public class InfoBean implements Serializable{
	
	private static final long serialVersionUID = 1L;
	
	private/*@ spec_public @*/ int  codice;
	private/*@ spec_public non_null @*/ String nome;
	private/*@ spec_public @*/ double costo;
	private/*@ spec_public non_null @*/ String descrizione;
	private/*@ spec_public @*/ int disponibilità;
	private/*@ spec_public non_null @*/ String tipologia;
	  
	public InfoBean()
	{
	 codice= -1;
     nome= " ";
	 costo= 0.0;
	 descrizione= " ";
	 disponibilità= 1;
	 tipologia= " ";
	}

	//@ pure
	public int getCodice()
	{
		return codice;
	}
	
	//@ pure
	public String getNome()
	{
		return nome;
	}
	
	//@ pure
	public double getCosto()
	{
		return costo;
	}

	//@ pure
	public String getDescrizione()
	{
		return descrizione;
	}
	
	//@ pure
	public int getDisponibilità()
	{
		return disponibilità;
	}
	
	//@ pure
	public String getTipologia()
	{
		return tipologia;
	}
	
	//@ assignable this.codice; 
	public void setCodice(int codice)
	{
		this.codice=codice;
	}
	
	//@ assignable this.nome; 
	public void setNome (String nome)
	{
		this.nome=nome;
	}
	
	//@ assignable this.costo; 
	public void setCosto (double costo)
	{
		this.costo=costo;
	}
	
	//@ assignable this.descrizione; 
	public void setDescrizione (String descrizione)
	{
		this.descrizione=descrizione;
	}
	
	//@ assignable this.disponibilità; 
	public void setDisponibilità (int disponibilità)
	{
		this.disponibilità=disponibilità;
	}
	
	//@ assignable this.tipologia; 
	public void setTipologia (String tipologia)
	{
		this.tipologia=tipologia;
	}
	

   //@ skipesc
	@Override
	public String toString() {
		return nome + " (" + codice + "), " + costo + " " + tipologia + ""+ disponibilità + ". " + descrizione;
	}
}
