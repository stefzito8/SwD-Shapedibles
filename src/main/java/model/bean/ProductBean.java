package model.bean;

import java.io.Serial;
import java.io.Serializable;
import java.util.Collection;
import java.util.Objects;

@SuppressWarnings("ALL")
public class ProductBean implements Serializable
{
	@Serial
	private static final long serialVersionUID = 1L;
	
	private /*@ spec_public @*/ int codice;
	private /*@ spec_public @*/ int infoCorrenti;
	private /*@ spec_public @*/ String nome;
	private /*@ spec_public nullable @*/ Collection<ImageBean> immagini;
	
	public ProductBean()
	{
	  codice= -1;
      infoCorrenti=-1;
      nome= " ";
	}
	
	//@ pure
	public int getCodice()
	{
		return codice;
	}
	
	//@ assignable this.codice; 
	public void setCodice(int codice)
	{
		this.codice=codice;
	}
	
	//@ pure
	public int getInfoCorrenti()
	{
		return infoCorrenti;
	}
	
	//@ assignable this.infoCorrenti; 
	public void setInfoCorrenti(int infoCorrenti)
	{
		this.infoCorrenti=infoCorrenti;
	}
	
	//@ pure
	public String getNome()
	{
		return nome;
	}
	
	//@ assignable this.nome; 
	public void setNome (String nome)
	{
		this.nome=nome;
	}
	
	//@ assignable this.immagini; 
	public void setImages (Collection<ImageBean> images) { this.immagini = images; }
	
	//@ pure
	public Collection<ImageBean> getImages() { return immagini; }

	//@  pure
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ProductBean that = (ProductBean) o;
        return Objects.equals(codice, that.codice);
    }
	
	//@  pure
    @Override
    public int hashCode() {
        return Objects.hash(codice);
    }
}
