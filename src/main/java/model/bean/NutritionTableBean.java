package model.bean;

import java.io.Serial;
import java.io.Serializable;

public class NutritionTableBean implements Serializable{

	@Serial
	private static final long serialVersionUID = 1L;
	
	int codice_prodotto;
	int energia;
	double grassi;
	double grassi_saturi;
	double carboedrati;
	double zucherri;
	double fibre;
	double proteine;
	double sale;
	
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
	
	public int getCodiceProdotto()
	{
		return codice_prodotto;
	}
	
	public int getEnergia()
	{
		return energia;
	}
	
	public double getGrassi()
	{
		return grassi;
	}
	
	public double getGrassiSaturi()
	{
		return grassi_saturi;
	}
	
	public double getCarboedrati()
	{
		return carboedrati;
	}
	
	public double getZucherri()
	{
		return zucherri;
	}
	
	public double getFibre()
	{
		return fibre;
	}
	
	public double getProteine()
	{
		return proteine;
	}
	
	public double getSale()
	{
		return sale;
	}
	
	public void setCodiceProdotto (int codice_prodotto)
	{
	  this.codice_prodotto=codice_prodotto;
	}
	
	public void setEnergia(int energia)
	{
		  this.energia=energia;
	}
	
	public void setGrassi(double grassi)
	{
		  this.grassi=grassi;
	}
	
	public void setGrassiSaturi(double grassi_saturi)
	{
		  this.grassi_saturi=grassi_saturi;
	}
	
	public void setCarboedrati(double carboedrati)
	{
		  this.carboedrati=carboedrati;
	}
	
	public void setZucherri(double zucherri)
	{
		  this.zucherri=zucherri;
	}
	
	public void setFibre(double fibre)
	{
		  this.fibre=fibre;
	}
	
	public void setProteine(double proteine)
	{
		  this.proteine=proteine;
	}
	
	public void setSale(double sale)
	{
		  this.sale=sale;
	}
	
	@Override
	public String toString() {
		return codice_prodotto + " " + energia + " " + grassi + " " + grassi_saturi + " " + carboedrati + " "+ zucherri + " " + fibre + " " + proteine + " " + sale;
	}
}

