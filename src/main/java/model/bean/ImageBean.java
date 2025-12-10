package model.bean;

import java.io.Serializable;

public class ImageBean implements Serializable
{

	private static final long serialVersionUID = 1L;
	private /*@ spec_public @*/ int numImage;
	private /*@ spec_public @*/ String img;
	private /*@ spec_public @*/ int codiceProdotto;
	
	public ImageBean()
	{
	   numImage=0;
	   img=" ";
	   codiceProdotto=0;
	}
	
	//@ assignable this.numImage; 
	public void setNumImage(int numImage)
	{
		this.numImage=numImage;
	}
	
	//@ assignable this.img; 
	public void setImg(String img)
	{
		this.img=img;
	}
	
	//@ assignable this.codiceProdotto; 
	public void setCodiceProdotto(int codiceProdotto)
	{
		this.codiceProdotto=codiceProdotto;
	}
	
	//@ pure
	public int getNumImage()
	{
		return numImage;
	}
	
	//@ pure
	public String getImg()
	{
		return img;
	}
	
	//@ pure
	public String getImgIfString(String string) {
		if (this.img.contains(string))
			return this.img;
		return null;
	}
	
	//@ pure
	public int getCodiceProdotto()
	{
		return codiceProdotto;
	}
	
	//@  pure
	@Override
	public String toString() {
		return numImage + " " + codiceProdotto + " " + img;
	}
}
