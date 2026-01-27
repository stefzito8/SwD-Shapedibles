package model.bean;

import java.io.Serializable;

public class ImageBean implements Serializable
{

	private static final long serialVersionUID = 1L;
	private int numImage;
	private String img;
	private int codiceProdotto;
	
	public ImageBean()
	{
	   numImage=0;
	   img=" ";
	   codiceProdotto=0;
	}
	
	public void setNumImage(int numImage)
	{
		this.numImage=numImage;
	}
	
	public void setImg(String img)
	{
		this.img=img;
	}
	
	public void setCodiceProdotto(int codiceProdotto)
	{
		this.codiceProdotto=codiceProdotto;
	}
	
	public int getNumImage()
	{
		return numImage;
	}
	
	public String getImg()
	{
		return img;
	}
	
	public String getImgIfString(String string) {
		if (this.img.contains(string))
			return this.img;
		return null;
	}
	
	public int getCodiceProdotto()
	{
		return codiceProdotto;
	}
	
	@Override
	public String toString() {
		return numImage + " " + codiceProdotto + " " + img;
	}
}
