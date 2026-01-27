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
	
	private int codice;
	private int infoCorrenti;
	String nome;
	private Collection<ImageBean> immagini;
	
	public ProductBean()
	{
	  codice= -1;
      infoCorrenti=-1;
      nome= " ";
	}
	
	public int getCodice()
	{
		return codice;
	}
	
	public void setCodice(int codice)
	{
		this.codice=codice;
	}
	
	public int getInfoCorrenti()
	{
		return infoCorrenti;
	}
	
	public void setInfoCorrenti(int infoCorrenti)
	{
		this.infoCorrenti=infoCorrenti;
	}
	
	public String getNome()
	{
		return nome;
	}
	
	public void setNome (String nome)
	{
		this.nome=nome;
	}
	
	public void setImages (Collection<ImageBean> images) { this.immagini = images; }
	
	public Collection<ImageBean> getImages() { return immagini; }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ProductBean that = (ProductBean) o;
        return Objects.equals(codice, that.codice);
    }

    @Override
    public int hashCode() {
        return Objects.hash(codice);
    }
}
