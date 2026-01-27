package model.bean;

import java.io.Serializable;

public class ContainBean implements Serializable{

	private static final long serialVersionUID = 1L;

	int codice_ordine;
	int codice_prodotto;
	int quantità;
	
	public ContainBean()
	{
		codice_ordine=-1;
		codice_prodotto=-1;
		quantità=1;
	}
	
	public int getCodiceOrdine()
	{
		return codice_ordine;
	}
	
	public int getCodiceProdotto()
	{
		return codice_prodotto;
	}
	
	public int getQuantità()
	{
		return quantità;
	}
	
	public void setCodiceOrdine(int codice_ordine)
	{
		this.codice_ordine=codice_ordine;
	}
	
	public void setCodiceProdotto(int codice_prodotto)
	{
		this.codice_prodotto=codice_prodotto;
	}
	
	public void setQuantità(int quantità)
	{
		this.quantità=quantità;
	}
	
	@Override
	public String toString() {
		return codice_ordine + " " + codice_prodotto + " " + quantità;
	}
}
