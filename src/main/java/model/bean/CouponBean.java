package model.bean;

import java.io.Serializable;

public class CouponBean implements Serializable{

	private static final long serialVersionUID = 1L;

	String codice;
	int percentuale_sconto;
	double saldo_minimo;
	
	public CouponBean()
	{
		codice=" ";
		percentuale_sconto=0;
		saldo_minimo= 0.0;
	}
	
	public String getCodice()
	{
		return codice;
	}
	
	public int getPercentualeSconto() 
	{
		return percentuale_sconto;
	}
	
	public double getSaldoMinimo()
	{
		return saldo_minimo;
	}
	
	public void setCodice(String codice)
	{
		this.codice=codice;
	}
	
	public void setPercentualeSconto(int percentuale_sconto)
	{
		this.percentuale_sconto=percentuale_sconto;
	}
	
	public void setSaldoMinimo(double saldo_minimo)
	{
		this.saldo_minimo=saldo_minimo;
	}
	
	@Override
	public String toString() {
		return codice + " " +percentuale_sconto + " " + saldo_minimo;
	}
}
