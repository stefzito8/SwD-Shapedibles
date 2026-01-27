package model.bean;

import java.io.Serial;
import java.io.Serializable;

public class NutritionTableBean implements Serializable{

	@Serial
	private static final long serialVersionUID = 1L;
	
	 private /*@ spec_public @*/int codice_prodotto;
	 private /*@ spec_public @*/int energia;
	 private /*@ spec_public @*/double grassi;
	 private /*@ spec_public @*/double grassi_saturi;
	 private /*@ spec_public @*/double carboedrati;
	 private /*@ spec_public @*/double zucherri;
	 private /*@ spec_public @*/double fibre;
	 private /*@ spec_public @*/double proteine;
	 private /*@ spec_public @*/double sale;
	
	public NutritionTableBean()
	{
	  codice_prodotto=-1;
	  energia=0;
	  grassi=0.0;
	  grassi_saturi=0.0;
	  carboedrati=0.0;
	  zucherri=0.0;
	  fibre=0.0;
	  proteine=0.0;
	  sale=0.0;
	}
	
	//@ pure
	public int getCodiceProdotto()
	{
		return codice_prodotto;
	}
	
	//@ pure
	public int getEnergia()
	{
		return energia;
	}
	
	//@ pure
	public double getGrassi()
	{
		return grassi;
	}
	
	//@ pure
	public double getGrassiSaturi()
	{
		return grassi_saturi;
	}
	
	//@ pure
	public double getCarboedrati()
	{
		return carboedrati;
	}
	
	//@ pure
	public double getZucherri()
	{
		return zucherri;
	}
	
	//@ pure
	public double getFibre()
	{
		return fibre;
	}
	
	//@ pure
	public double getProteine()
	{
		return proteine;
	}
	
	//@ pure
	public double getSale()
	{
		return sale;
	}
	
	//@ assignable this.codice_prodotto;
	public void setCodiceProdotto (int codice_prodotto)
	{
	  this.codice_prodotto=codice_prodotto;
	}
	
	//@ assignable this.energia;
	public void setEnergia(int energia)
	{
		  this.energia=energia;
	}
	
	//@ assignable this.grassi;
	public void setGrassi(double grassi)
	{
		  this.grassi=grassi;
	}
	
	//@ assignable this.grassi_saturi;
	public void setGrassiSaturi(double grassi_saturi)
	{
		  this.grassi_saturi=grassi_saturi;
	}
	
	//@ assignable this.carboedrati;
	public void setCarboedrati(double carboedrati)
	{
		  this.carboedrati=carboedrati;
	}
	
	//@ assignable this.zucherri;
	public void setZucherri(double zucherri)
	{
		  this.zucherri=zucherri;
	}
	
	//@ assignable this.fibre;
	public void setFibre(double fibre)
	{
		  this.fibre=fibre;
	}
	
	//@ assignable this.proteine;
	public void setProteine(double proteine)
	{
		  this.proteine=proteine;
	}
	
	//@ assignable this.sale;
	public void setSale(double sale)
	{
		  this.sale=sale;
	}
	
	//@ pure
	@Override
	public String toString() {
		return codice_prodotto + " " + energia + " " + grassi + " " + grassi_saturi + " " + carboedrati + " "+ zucherri + " " + fibre + " " + proteine + " " + sale;
	}
}

