package model.bean;

import java.io.Serializable;

public class InfoBean implements Serializable{
	
	private static final long serialVersionUID = 1L;
	
	int codice;
	String nome;
	double costo;
	String descrizione;
	int disponibilità;
	String tipologia;
	  
	public InfoBean()
	{
	 codice= -1;
     nome= " ";
	 costo= 0.0;
	 descrizione= " ";
	 disponibilità= 1;
	 tipologia= " ";
	}
	
	public int getCodice()
	{
		return codice;
	}
	
	public String getNome()
	{
		return nome;
	}
	
	public double getCosto()
	{
		return costo;
	}
	
	public String getDescrizione()
	{
		return descrizione;
	}
	
	public int getDisponibilità()
	{
		return disponibilità;
	}
	
	public String getTipologia()
	{
		return tipologia;
	}
	
	public void setCodice(int codice)
	{
		this.codice=codice;
	}
	
	public void setNome (String nome)
	{
		this.nome=nome;
	}
	
	public void setCosto (double costo)
	{
		this.costo=costo;
	}
	
	public void setDescrizione (String descrizione)
	{
		this.descrizione=descrizione;
	}
	
	public void setDisponibilità (int disponibilità)
	{
		this.disponibilità=disponibilità;
	}
	
	public void setTipologia (String tipologia)
	{
		this.tipologia=tipologia;
	}
	
	 
	@Override
	public String toString() {
		return nome + " (" + codice + "), " + costo + " " + tipologia + ""+ disponibilità + ". " + descrizione;
	}
}
