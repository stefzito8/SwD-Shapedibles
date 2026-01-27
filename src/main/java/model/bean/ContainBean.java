package model.bean;

import java.io.Serializable;

public class ContainBean implements Serializable{

	private static final long serialVersionUID = 1L;

	private /*@ spec_public @*/ int codice_ordine;
	private /*@ spec_public @*/ int codice_prodotto;
	private /*@ spec_public @*/ int quantità;
	
	public ContainBean()
	{
		codice_ordine=-1;
		codice_prodotto=-1;
		quantità=1;
	}
	
	//@ pure
	public int getCodiceOrdine()
	{
		return codice_ordine;
	}
	
	//@ pure
	public int getCodiceProdotto()
	{
		return codice_prodotto;
	}
	
	//@ pure
	public int getQuantità()
	{
		return quantità;
	}
	
	//@ assignable this.codice_ordine;
	public void setCodiceOrdine(int codice_ordine)
	{
		this.codice_ordine=codice_ordine;
	}
	
	//@ assignable this.codice_prodotto;
	public void setCodiceProdotto(int codice_prodotto)
	{
		this.codice_prodotto=codice_prodotto;
	}
	
	//@ assignable this.quantità;
	public void setQuantità(int quantità)
	{
		this.quantità=quantità;
	}
	
	//@ pure
	@Override
	public String toString() {
		return codice_ordine + " " + codice_prodotto + " " + quantità;
	}
}
