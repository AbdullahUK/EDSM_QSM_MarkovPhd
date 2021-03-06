/* Copyright (c) 2011 Neil Walkinshaw and Kirill Bogdanov
 * 
 * This file is part of StateChum.
 * 
 * StateChum is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * StateChum is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with StateChum.  If not, see <http://www.gnu.org/licenses/>.
 */

/*
 * Installation of RJava, JavaGD and aplpack on Debian x86_64:
 * apt-get install r-base
 * 
 * (note: an alternative way to install javagd is from http://blog.binfalse.de/2011/02/talking-r-through-java/
 *  which boils down to apt-get install r-cran-rjava 
 * Asking R to install packages itself will fail on a PAX-enabled system because binaries it generates does not have
 * mprotect disabled, to make this work you have to change every line in the two configure files of rJava which 
 * says 
 * ac_try='./conftest$ac_exeext' 
 * to read
 * ac_try='paxctl -Cm ./conftest$ac_exeext;./conftest$ac_exeext'
 * After that, configure will be successful. The outcome can be turned back into rJava.tar.gz and R will install it via
 * install.packages("/tmp/RtmpxtSS7S/downloaded_packages/rJava-modified.tar.gz")
 * As root:
 * 
 * R CMD javareconf
 * 
 * (it uses getsp.java also available in JavaGD distribution (getsp.java takes java.library.path and splits it into segments prefixed by -L ,
 * on Debian it is stored in /usr/share/R/share/java/getsp.class )
 * Note that R CMD config CC obtains C compiler for R, similar for other flags.
 * 
 * Then unpack JavaGD into /usr/local/src/JavaGD and then run
 * 
 * R CMD INSTALL JavaGD
 * 
 * from /usr/local/src, this builds and installs the package.
 * 
 * In a similar way, I can install rJava, but perhaps it is prudent to disable extra package loading via JRIBootstrap.java
 * 
 * During installation packages are placed in /usr/local/lib/R/site-library and I have to include /usr/local/lib/R/site-library/rJava/jri/ in java.library.path
 * In addition, R_HOME has to be set to /usr/lib/R (in Eclipse Run configuration).
 * 
 * In order to use bagplots, the following is needed,
 * R CMD INSTALL aplpack
 * 
 * Installation of the above on MacOSX and Win32:
 * 
 * install.packages(c("JavaGD","rJava","aplpack"))
 * On MacOS, tcltk is a special download which installs into /usr/local.
 * 
 * Where R is install from Macports, I need to installed both as follows:
 * <pre>
 * port install tk +x11
 * port install R +gfortran48 +x11 +tcltk
 * </pre>
 * Installing a pre-built binary from R web site does not work because it is linked to Quartz that appears to be missing, most likely because they have used Lion or something similar).
 * 
 * R_HOME needs to be set to /opt/local/Library/Frameworks/R.framework/Resources
 * and /opt/local/Library/Frameworks/R.framework/Versions/3.0/Resources/library/rJava/jri needs adding to java.library.path
 * 
 */


// This file is based on rtest.java

package statechum.analysis.learning;
import java.awt.geom.Rectangle2D;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;

import javax.swing.SwingUtilities;

import org.rosuda.JRI.REXP;
import org.rosuda.JRI.RMainLoopCallbacks;
import org.rosuda.JRI.Rengine;

import statechum.Configuration;
import statechum.GlobalConfiguration;
import statechum.GlobalConfiguration.G_PROPERTIES;
import statechum.Helper;

public class DrawGraphs {
	/** Determines whether our callbacks are dummies (without a main loop) or active (main loop running).
	 */
	static boolean mainLoopRunning = false;
	
	public static class ConsoleCallbacks implements RMainLoopCallbacks
	{

		@SuppressWarnings("unused")
		@Override
		public void rBusy(Rengine arg0, int arg1) {
			// dummy
		}

		@SuppressWarnings("unused")
		@Override
		public String rChooseFile(Rengine arg0, int arg1) {
			// dummy
			return null;
		}

		@SuppressWarnings("unused")
		@Override
		public void rFlushConsole(Rengine arg0) {
			// dummy
		}

		@SuppressWarnings("unused")
		@Override
		public void rLoadHistory(Rengine arg0, String arg1) {
			// dummy
		}

        private BufferedReader br=new BufferedReader(new InputStreamReader(System.in));

        /** Mostly from rtest.java */
        @SuppressWarnings("unused")
		@Override
		public String rReadConsole(Rengine arg0, String prompt, int arg2) {
        	if (!mainLoopRunning) return null;
        	
	       System.out.print(prompt);
	        try {
	            String s=br.readLine();
	            return (s==null||s.length()==0)?s:s+"\n";
	        } catch (Exception e) {
	            System.out.println("rReadConsole exception: "+e.getMessage());
	        }
	        return null;
		}

		@SuppressWarnings("unused")
		@Override
		public void rSaveHistory(Rengine arg0, String arg1) {
			// dummy
		}

		@SuppressWarnings("unused")
		@Override
		public void rShowMessage(Rengine arg0, String arg1) {
			if (mainLoopRunning) System.out.println(arg1);
		}

		@SuppressWarnings("unused")
		@Override
		public void rWriteConsole(Rengine arg0, String arg1, int arg2) {
			if (mainLoopRunning) System.out.println(arg1);
			else
			{
				consoleBuffer.append(arg1);consoleBuffer.append('\n');
			}
		}
		
		private StringBuffer consoleBuffer = new StringBuffer();
		
		public void clearBuffer()
		{
			consoleBuffer = new StringBuffer();
		}
		
		public String getBuffer()
		{
			return consoleBuffer.toString();
		}
	}
	
	/** R engine - can only be initalised once - second time packages do not load ("setwd(x) cannot change directory")
	 * because F:/R/windows64/R-2.12.2/library is passed to setwd and even if the correct value is passed, package
	 * loading fails.
	 */
	protected static Rengine engine;
	protected static ConsoleCallbacks callbacks = new ConsoleCallbacks();
	
	public DrawGraphs()
	{
		java.lang.reflect.Method loadJri = null;
			
		try
		{
			loadJri = Rengine.class.getMethod("loadJri", new Class[]{String.class});
		} catch (Exception e)
		{// ignore this, loadJri remains null.
		}
		
		try
		{
			if (loadJri != null && !((Boolean)loadJri.invoke(null, GlobalConfiguration.getConfiguration().getProperty(G_PROPERTIES.PATH_JRILIB))).booleanValue())
				throw new IllegalArgumentException("JRI library could not be loaded");
		} catch (IllegalAccessException e)
		{
			throw new IllegalArgumentException("Calling a method to load JRI library failed",e);
		} catch (InvocationTargetException e)
		{
			throw new IllegalArgumentException("Calling a method to load JRI library failed",e);
		} // IllegalArgumentException thrown by the above should propagate

		if (!Rengine.versionCheck()) 
			throw new IllegalArgumentException("R version mismatch");
		if (engine == null)
		{
			engine = new Rengine(new String[]{"--vanilla"},false,callbacks);
			//engine.setDaemon(true);
			if (!engine.waitForR())
				throw new IllegalArgumentException("loading R failed");

			Runtime.getRuntime().addShutdownHook(new Thread() {
			    @Override
				public void run() { 
			    	end();
			    }
			});
			eval("library(aplpack)","loading BagPlot");

			// detect if compression is supported
			pdfCompression = eval("is.element(\"compress\",names(formals(pdf)))","failed to detect whether compression is supported").asBool().isTRUE();
		}
	}

	protected static REXP eval(String whatToEval, String errMsg)
	{
		
		callbacks.clearBuffer();
		REXP result = engine.eval(whatToEval);
		if (result == null)
			throw new IllegalArgumentException(errMsg+" : "+callbacks.getBuffer());
	
		return result;
	}
	
	protected static StatsticatTestResult eval1(String whatToEval, String errMsg)
	{
		StatsticatTestResult STR=new StatsticatTestResult();

		callbacks.clearBuffer();
		REXP result = engine.eval(whatToEval);
		if (result == null)
			throw new IllegalArgumentException(errMsg+" : "+callbacks.getBuffer());

		if(whatToEval.startsWith("m="))
		{
			STR.statistic=engine.eval("m$statistic").asDouble();
			STR.pvalue=engine.eval("m$p.value").asDouble();
			STR.Method=engine.eval("m$method").asString();
			STR.alternative=engine.eval("m$alternative").asString();
			STR.parameter=engine.eval("m$parameter").asDouble();
		}	
		return STR;
	}

	protected static <ELEM> String vectorToR(List<ELEM> vector, boolean addQuotes)
	{
		if (vector.size() == 0) throw new IllegalArgumentException("cannot plot an empty graph");
		StringBuffer result = new StringBuffer();
		result.append("c(");
		boolean startVector = true;
		for(ELEM elem:vector)
		{
			if (!startVector) result.append(",");else startVector=false;
			if (addQuotes) 	result.append('\"');
			result.append(elem);
			if (addQuotes) 	result.append('\"');
		}
		result.append(")");
		return result.toString();
	}
	
	public static final String defaultColour = "green";
	
	/**
	 * Formats a box plotting command to R.
	 * 
	 * @param data what to plot
	 * @param names names of boxes
	 * @param colour colour of boxes
	 * @param otherAttrs additional attributes to set, null if not used.
	 * @return The string to be sent to R for evaluation.
	 */
	protected static String boxPlotToString(List<List<Double>> data,List<String> names,List<String> colour, String otherAttrs)
	{
		if (data.size() == 0) throw new IllegalArgumentException("cannot plot an empty graph");
		if (data.size() == 1 && names != null) throw new IllegalArgumentException("in a graph with one component, names are not used");
		if (data.size() > 1 && names != null && names.size() != data.size()) throw new IllegalArgumentException("mismatch between name and data length"); 
		StringBuffer result = new StringBuffer();
		result.append("boxplot(");
		boolean firstVectorOfData = true;
		for(List<Double> arg:data)
		{
			if (!firstVectorOfData) result.append(",");else firstVectorOfData=false;
			result.append(vectorToR(arg,false));
		}
		
		// names
		if (names != null)
		{
			result.append(",names=");
			result.append(vectorToR(names, true));
		}
		
		// colours
		{
			result.append(",col=");
			if (colour != null) result.append(vectorToR(colour,true));
			else
			{// no colours provided, using the default one
				boolean startVector = true;
				result.append("c(");
				for(int i=0;i<data.size();++i)
				{
					if (!startVector) result.append(",");else startVector=false;
					result.append('\"');
					String col = defaultColour;
					result.append(col);
					result.append('\"');
				}
				result.append(")");
			}
		}
		if (otherAttrs != null) { result.append(',');result.append(otherAttrs); }
		result.append(")");
		return result.toString();
	}
	
	
	
	
	/**
	 * Formats a WilcoxonTest command to R.
	 * 
	 * @param data that represent x in the wilcox.test(X,y,paired=TRUE) 
	 * @param data1 that represent Y in the wilcox.test(X,y,paired=TRUE) 
	 * @return The string to be sent to R for evaluation.
	 */
	protected static String WilcoxonTest(List<Double> data,List<Double> data1,List<String> names,List<String> colour, String otherAttrs)
	{
		if (data.size() == 0 || data1.size()==0) throw new IllegalArgumentException("cannot plot an empty graph");
		if (data.size() != data1.size()) throw new IllegalArgumentException(" 'x' and 'y' must have the same length");

		StringBuffer result = new StringBuffer();
		result.append("m=wilcox.test(");
		
		result.append(vectorToR(data,false));
		result.append(",");
		result.append(vectorToR(data1,false));

		result.append(",paired=TRUE");

		result.append(")");
		return result.toString();
	}
	
	/**
	 * Formats a Mann-Whitney U Test command to R.
	 * 
	 * @param data that represent x in the wilcox.test(X,y,paired=TRUE) 
	 * @param data1 that represent Y in the wilcox.test(X,y,paired=TRUE) 
	 * @return The string to be sent to R for evaluation.
	 */
	protected static String Mann_Whitney_U_Test(List<Double> data,List<Double> data1,List<String> names,List<String> colour, String otherAttrs)
	{
		if (data.size() == 0 || data1.size()==0) throw new IllegalArgumentException("cannot plot an empty graph");

		StringBuffer result = new StringBuffer();
		result.append("m=wilcox.test(");
		result.append(vectorToR(data,false));
		result.append(",");
		result.append(vectorToR(data1,false));

		result.append(")");
		return result.toString();
	}
	
	
	/**
	 * Formats a Kruskal-Wallis Test command to R.
	 * 
	 * @param data that represent x in the wilcox.test(X,y,paired=TRUE) 
	 * @param data1 that represent Y in the wilcox.test(X,y,paired=TRUE) 
	 * @return The string to be sent to R for evaluation.
	 */
	protected static String Kruskal_Wallis_Test(List<Double> data,List<Double> data1,List<String> names,List<String> colour, String otherAttrs)
	{
		if (data.size() == 0 || data1.size()==0) throw new IllegalArgumentException("cannot plot an empty graph");
		if (data.size() != data1.size()) throw new IllegalArgumentException("'x' and 'y' must have the same length");

		StringBuffer result = new StringBuffer();
		result.append("m=kruskal.test(");
		result.append(vectorToR(data,false));
		result.append(",");
		result.append(vectorToR(data1,false));

		result.append(")");
		return result.toString();
	}
	
	/**
	 * Formats a bag plotting command to R.
	 * 
	 * @param yData what to plot vertically
	 * @param xData what to plot horizontally
	 * @param otherAttrs additional attributes to set, null if not used.
	 * @return The string to be sent to R for evaluation.
	 */
	protected static String datasetToString(String plotType,List<List<Double>> yData,List<Double> xData, String otherAttrs)
	{
		if (yData.size() == 0) throw new IllegalArgumentException("cannot plot an empty graph");
		if (yData.size() != xData.size()) throw new IllegalArgumentException("mismatch between x and y length"); 
		StringBuffer result = new StringBuffer();
		result.append(plotType);result.append("(");
		StringBuffer yAxisData = new StringBuffer();
		Iterator<Double> xArgIterator = xData.iterator();
		result.append("c(");yAxisData.append(",c(");
		boolean startVector = true;
		for(List<Double> yArg:yData)
		{
			Double xArg = xArgIterator.next();
			for(Double elem:yArg)
			{
				if (!startVector) { yAxisData.append(",");result.append(','); } else startVector=false;
				yAxisData.append(elem);result.append(xArg);
			}
		}
		result.append(')');yAxisData.append(')');
		result.append(yAxisData);

		if (otherAttrs != null && !otherAttrs.isEmpty()) { result.append(',');result.append(otherAttrs); }
		result.append(")");
		return result.toString();
	}
	
	private static boolean javaGDLoaded = false;
	
	/** Newer versions of R permit pdf compression, but older ones choke if I attempt to use it. 
	 */
	private static boolean pdfCompression = false;
	
	/** Since I cannot pass arguments to RViewer during it construction, static values have to be set and 
	 * then copied into the new object. For this reason, creation of graphs has to be serialised, this is done
	 * by running it all on the Swing thread (avoids a deadlock associated with resizing of the window
	 * and us doing something to it at the same time on different threads).
	 */
	public void drawInteractivePlot(final List<String> dataToPlot,final String title)
	{
		// First, load javaGD
		if (!javaGDLoaded)
		{
			// based on http://www.algorithm-forge.com/techblog/2010/07/using-javagd-in-java-applications/
			engine.eval(".setenv <- if (exists(\"Sys.setenv\")) Sys.setenv else Sys.putenv");
			engine.eval(".setenv(\"JAVAGD_CLASS_NAME\"=\"statechum/analysis/learning/RViewer\")");
			eval("library(JavaGD)","loading JavaGD");
			
			javaGDLoaded = true;
		}

		try {
			SwingUtilities.invokeAndWait(new Runnable() {
				@Override
				public void run()
				{
					if (RViewer.getGraph(title) == null)
					{// create new graph
						RViewer.setNewGraphName(title);
						eval("JavaGD(\"aa\")","JavaGD() failed");
						REXP devNum = eval("dev.cur()","failed to do dev.cur");
						
						RViewer.getGraph(title).init(devNum.asInt()-1);
					}
					eval("dev.set("+(RViewer.getGraph(title).getDeviceNumber()+1)+")","failed to do dev.set for "+title);
					for(String cmd:dataToPlot)
						eval(cmd,"failed to run plot "+cmd);
				}
			});
		} catch (Exception e) {
			Helper.throwUnchecked("could not draw graph "+title, e);
		}
	}


	/** Draws a plot given the data to plot and stores it in the given file.
	 * 
	 * @param drawingCommand drawing command to pass to R
	 * @param xDim horizontal size in inches, R default is 7.
	 * @param yDim vertical size in inches, R default is 7.
	 * @param fileName where to store result.
	 */
	public void drawPlot(List<String> drawingCommand,double xDim,double yDim,File file)
	{
		if (xDim < 1) 
			throw new IllegalArgumentException("horizontal size ("+xDim+") too small");
		if (yDim < 1) throw new IllegalArgumentException("vertical size ("+yDim+") too small");
		
		if (file.exists() && file.delete() == false)
			throw new IllegalArgumentException("cannot delete file "+file.getAbsolutePath());
		// Slashes have to be the Unix-way - R simply terminates the DLL on WinXP otherwise.
		String fullName = file.getAbsolutePath().replace(File.separatorChar, '/');
		eval("pdf(\""+fullName+"\","+xDim+","+yDim
				+(pdfCompression?",compress=FALSE":"") // disable pdf compression if enabled
				+")","redirection to pdf("+file.getAbsolutePath()+") failed");
		for(String cmd:drawingCommand)
			eval(cmd,"failed to run "+cmd);
		eval("dev.off()","failed to write to "+file.getAbsolutePath());
	}
	
	/** Draws a plot given the data to plot and stores it in the given file.
	 * 
	 * @param drawingCommand drawing command to pass to R
	 * @param xDim horizontal size in inches, R default is 7.
	 * @param yDim vertical size in inches, R default is 7.
	 * @param fileName where to store result.
	 */
	public StatsticatTestResult CollectResultStatsticalResult(List<String> drawingCommand)
	{
		StatsticatTestResult STR=new StatsticatTestResult();
		for(String cmd:drawingCommand)
			STR=eval1(cmd,"failed to run "+cmd);
		return STR;
		
	}
	
	/**
	 * Shuts down jri thread - since jri is not a daemon thread JVM will not exit if this is not called.
	 */
	public static void end()
	{
		if (engine != null) 
		{
			for(RViewer v:RViewer.nameToGraph.values())	v.gdClose();
			engine.end();
			engine=null;	
		}		
	}

	public static class DataColumn
	{
		/** Data to be displayed. */
		final List<Double> results;
		/** Colour to use, if {@code null} default colour is used. */
		String colour;
		/** Label to be used, if {@code null} column identifier is used. */
		String label;
		
		public DataColumn()
		{
			results = new ArrayList<Double>(1000); 
		}
	}
	
	/**
	 * A version DataColoumn method that allow the user to store two results in a MAP <ELEM,DataColumnPairValues>();
	 *  where DataColumnPairValues has pair of value to add each time
	 */
	public static class DataColumnPairValues
	{
		/** Data to be displayed. */
		final List<Double> results;
		final List<Double> results1;

		/** Colour to use, if {@code null} default colour is used. */
		String colour;
		/** Label to be used, if {@code null} column identifier is used. */
		String label;
		
		public DataColumnPairValues()
		{
			results = new ArrayList<Double>(1000); 
			results1 = new ArrayList<Double>(1000); 

		}
	}
	
	/**
	 * Represents a graph.
	 * 
	 * @param <ELEM> type of elements for the X axis, vertical is always a Double
	 */
	public static abstract class RGraph<ELEM extends Comparable<? super ELEM>>
	{
		Map<ELEM,DataColumn> collectionOfResults = new TreeMap<ELEM,DataColumn>();
		
		// it is added to use them for some computation such as WilcoxonTest
		Map<ELEM,DataColumnPairValues> collectionOfResults2 = new TreeMap<ELEM,DataColumnPairValues>();
		Map<ELEM,DataColumn> collectionOfResults3 = new TreeMap<ELEM,DataColumn>();

		protected final String xAxis,yAxis;
		protected final File file;
		
		/** Number of entries in the graph. */
		protected int size = 0;
		
		/** Additional drawing command to append to a plot, such as abline() command. */
		protected List<String> extraCommands = new LinkedList<String>();
		
		public void addExtraCommand(String cmd)
		{
			extraCommands.add(cmd);
		}
		
		public RGraph(String x,String y,File name)
		{
			xAxis=x;yAxis=y;file=name;
		}
		
		protected ELEM xMin = null, xMax = null;
		protected Double yMin = null, yMax = null;
		
		public void setXboundaries(ELEM min, ELEM max)
		{
			xMin = min;xMax = max;
		}
		
		public void setYboundaries(double min, double max)
		{
			yMin = min;yMax = max;
		}
		
		public synchronized void add(ELEM el,Double value)
		{
			if (yMin != null && yMin.doubleValue() > value.doubleValue()) return;
			if (yMax != null && yMax.doubleValue() < value.doubleValue()) return;
			
			if (xMin != null && xMin.compareTo(el) > 0) return;
			if (xMax != null && xMax.compareTo(el) < 0) return;
			
			DataColumn column = collectionOfResults.get(el);
			if (column == null) { column=new DataColumn();collectionOfResults.put(el,column); }
			column.results.add(value);
			++size;
		}
		
		public synchronized void addExcel(ELEM el,Double value)
		{
			if (yMin != null && yMin.doubleValue() > value.doubleValue()) return;
			if (yMax != null && yMax.doubleValue() < value.doubleValue()) return;
			
			if (xMin != null && xMin.compareTo(el) > 0) return;
			if (xMax != null && xMax.compareTo(el) < 0) return;
			
			DataColumn column = collectionOfResults3.get(el);
			if (column == null) { column=new DataColumn();collectionOfResults3.put(el,column); }
			column.results.add(value);
			++size;
		}
		
		public synchronized void add(ELEM el,Double value, String colour)
		{
			add(el,value);collectionOfResults.get(el).colour=colour;
		}
		
		public int size()
		{
			return size;
		}
		
		/** Same as {@link add} but additionally permits setting of both colour and a label for this 
		 * column of data values.
		 * @param el identifier for the column
		 * @param value value to be added to it
		 * @param colour colour with which box plot values are to be shown
		 * @param label label to show on the horizonal axis, empty string for no label.
		 */
		public synchronized void add(ELEM el,Double value, String colour, String label)
		{
			add(el,value);
			if (colour != null) collectionOfResults.get(el).colour=colour;
			if (label != null) collectionOfResults.get(el).label=label;
		}
		
		
		public synchronized void addPairValues(ELEM el,Double value, String colour, String label)
		{
			DataColumnPairValues column = collectionOfResults2.get(el);
			if (column == null) { column=new DataColumnPairValues();collectionOfResults2.put(el,column); }
			column.results.add((Double) el);
			column.results1.add(value);
			++size;
		}
		
		public synchronized void addExcel(ELEM el,Double value, String colour, String label)
		{
			addExcel(el,value);
			if (colour != null) collectionOfResults3.get(el).colour=colour;
			if (label != null) collectionOfResults3.get(el).label=label;
		}
		
		
		
		
		/** Returns a command to draw a graph in R. */
		protected abstract List<String> getDrawingCommand();
		protected abstract Map<String, List<Double>> get_Table();

		public void drawInteractive(DrawGraphs gr)
		{
			List<String> drawingCommands = new LinkedList<String>();
			drawingCommands.addAll(getDrawingCommand());drawingCommands.addAll(extraCommands);
			gr.drawInteractivePlot(drawingCommands, file.getName());
		}
		
		protected double xSize = -1;
		
		/** Sets the horizonal size of the plot, vertical size is always set to 4 inches. 
		 * If no assignemnt is made, the size is guessed from the number of points on the drawing. 
		 */ 
		public void setXSize(double newSize)
		{
			xSize = newSize;
		}
		
		double ySize = 5;

		public void drawPdf(DrawGraphs gr)
		{
			if (collectionOfResults.size() > 0)
			{
				double horizSize = xSize;
				if (horizSize <= 0) horizSize=computeHorizSize();
				List<String> drawingCommands = new LinkedList<String>();
				drawingCommands.addAll(getDrawingCommand());drawingCommands.addAll(extraCommands);
				gr.drawPlot(drawingCommands, horizSize,ySize,file);

			}
			else
				if (collectionOfResults2.size() > 0)
				{
					double horizSize = xSize;
					if (horizSize <= 0) horizSize=computeHorizSize();
					List<String> drawingCommands = new LinkedList<String>();
					drawingCommands.addAll(getDrawingCommand());drawingCommands.addAll(extraCommands);
					gr.writetofile(drawingCommands,gr,file);
				}
				else
					if (collectionOfResults3.size() > 0)
					{
						double horizSize = xSize;
						if (horizSize <= 0) horizSize=computeHorizSize();
						Map<String , List<Double>> list = get_Table();

						gr.writingExcelFile(list,gr,file);
					}					
			else
				if (GlobalConfiguration.getConfiguration().isAssertEnabled())
					System.out.println("WARNING: ignoring empty plot that was supposed to be written into "+file);
		}
		
		/* Computes the horizontal size of the drawing. */
		abstract protected double computeHorizSize();
		
		/** Reports the name of the file with the graph, used for identification of different graphs. */
		public String getFileName()
		{
			return file.getName();
		}	
	}
	
	public static class RBoxPlot<ELEM extends Comparable<? super ELEM>> extends RGraph<ELEM>
	{
		public RBoxPlot(String x, String y, File name) {
			super(x, y, name);
		}
		
		@Override
		public List<String> getDrawingCommand()
		{
			List<List<Double>> data = new LinkedList<List<Double>>();
			List<String> names = new LinkedList<String>(), colours = new LinkedList<String>();
			for(Entry<ELEM,DataColumn> entry:collectionOfResults.entrySet())
			{
				data.add(entry.getValue().results);
				String label = entry.getValue().label;
				if (label == null)
					label = entry.getKey().toString();
				names.add(label);
				String colour = entry.getValue().colour;
				if (colour == null) colour = defaultColour;
				colours.add(colour);
			}
			return Collections.singletonList(boxPlotToString(data, names.size()==1?null:names,colours,
					(!xAxis.isEmpty() || !yAxis.isEmpty())?	"xlab=\""+xAxis+"\",ylab=\""+yAxis+"\""
					:null		
					));
		}

		@Override
		protected double computeHorizSize() {
			double horizSize=ySize*collectionOfResults.keySet().size()/5;if (horizSize < ySize) horizSize = ySize;
			return horizSize;
		}

		@Override
		protected Map<String , List<Double>> get_Table() {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	
	
	public static class RBoxPlotCvs<ELEM extends Comparable<? super ELEM>> extends RGraph<ELEM>
	{
		public RBoxPlotCvs(String x, String y, File name) {
			super(x, y, name);
		}
		
		@Override
		public Map<String , List<Double>> get_Table()
		{
		    Map<String, List<Double>> ListOfContent= new TreeMap<String, List<Double>>();

			List<List<Double>> data = new LinkedList<List<Double>>();
			int i=0;
			for(Entry<ELEM,DataColumn> entry:collectionOfResults3.entrySet())
			{
				data.add(entry.getValue().results);
				ListOfContent.put(entry.getKey().toString(), data.get(i));
				i++;
			}
			return ListOfContent;
		}

		@Override
		protected double computeHorizSize() {
			double horizSize=ySize*collectionOfResults.keySet().size()/5;if (horizSize < ySize) horizSize = ySize;
			return horizSize;
		}


		@Override
		protected List<String> getDrawingCommand() {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	public static class RBoxPlotP<ELEM extends Comparable<? super ELEM>> extends RGraph<ELEM>
	{
		public RBoxPlotP(String x, String y, File name) {
			super(x, y, name);
		}
		
		@Override
		public List<String> getDrawingCommand()
		{
			List<List<Double>> data = new LinkedList<List<Double>>();
			List<String> names = new LinkedList<String>(), colours = new LinkedList<String>();
			for(Entry<ELEM,DataColumn> entry:collectionOfResults.entrySet())
			{
				data.add(entry.getValue().results);
				String label = entry.getValue().label;
				if (label == null)
					label = entry.getKey().toString();
				names.add(label);
				String colour = entry.getValue().colour;
				if (colour == null) colour = defaultColour;
				colours.add(colour);
			}
			return Collections.singletonList(boxPlotToString(data, names.size()==1?null:names,colours,"xlab=\""+xAxis+"\",ylab=\""+yAxis+"\",las=2"));
		}

		@Override
		protected double computeHorizSize() {
			double horizSize=ySize*collectionOfResults.keySet().size()/5;if (horizSize < ySize) horizSize = ySize;
			return horizSize;
		}

		@Override
		protected Map<String , List<Double>> get_Table() {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	
	public static class Wilcoxon<ELEM extends Comparable<? super ELEM>> extends RGraph<ELEM>
	{
		public Wilcoxon(String x, String y, File name) {
			super(x, y, name);
		}
		
		@Override
		public List<String> getDrawingCommand()
		{
			List<Double> data = new LinkedList<Double>();
			List<Double> data1 = new LinkedList<Double>();
			List<String> names = new LinkedList<String>(), colours = new LinkedList<String>();
			for(Entry<ELEM, DataColumnPairValues> entry:collectionOfResults2.entrySet())
			{
				data.addAll(entry.getValue().results);
				data1.addAll(entry.getValue().results1);

				String label = entry.getValue().label;
				if (label == null)
					label = entry.getKey().toString();
				names.add(label);
				String colour = entry.getValue().colour;
				if (colour == null) colour = defaultColour;
				colours.add(colour);
			}
			return Collections.singletonList(WilcoxonTest(data, data1,names.size()==1?null:names,colours,"xlab=\""+xAxis+"\",ylab=\""+yAxis+"\",las=2"));
		}

		@Override
		protected double computeHorizSize() {
			double horizSize=ySize*collectionOfResults.keySet().size()/5;if (horizSize < ySize) horizSize = ySize;
			return horizSize;
		}

		@Override
		protected Map<String , List<Double>> get_Table() {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	
	public static class RWilcoxon<ELEM extends Comparable<? super ELEM>> extends RGraph<ELEM>
	{
		public RWilcoxon(String x, String y, File name) {
			super(x, y, name);
		}
		
		@Override
		public List<String> getDrawingCommand()
		{
			List<Double> data = new LinkedList<Double>();
			List<Double> data1 = new LinkedList<Double>();
			List<String> names = new LinkedList<String>(), colours = new LinkedList<String>();
			for(Entry<ELEM, DataColumnPairValues> entry:collectionOfResults2.entrySet())
			{
				data.addAll(entry.getValue().results);
				data1.addAll(entry.getValue().results1);

				String label = entry.getValue().label;
				if (label == null)
					label = entry.getKey().toString();
				names.add(label);
				String colour = entry.getValue().colour;
				if (colour == null) colour = defaultColour;
				colours.add(colour);
			}
			return Collections.singletonList(WilcoxonTest(data,data1, names.size()==1?null:names,colours,
					(!xAxis.isEmpty() || !yAxis.isEmpty())?	"xlab=\""+xAxis+"\",ylab=\""+yAxis+"\""
					:null		
					));
		}

		@Override
		protected double computeHorizSize() {
			double horizSize=ySize*collectionOfResults.keySet().size()/5;if (horizSize < ySize) horizSize = ySize;
			return horizSize;
		}

		@Override
		protected Map<String , List<Double>> get_Table() {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	
	public static class Mann_Whitney_U_Test<ELEM extends Comparable<? super ELEM>> extends RGraph<ELEM>
	{
		public Mann_Whitney_U_Test(String x, String y, File name) {
			super(x, y, name);
		}
		
		@Override
		public List<String> getDrawingCommand()
		{
			List<Double> data = new LinkedList<Double>();
			List<Double> data1 = new LinkedList<Double>();

			List<String> names = new LinkedList<String>(), colours = new LinkedList<String>();
			for(Entry<ELEM, DataColumnPairValues> entry:collectionOfResults2.entrySet())
			{
				data.addAll(entry.getValue().results);
				data1.addAll(entry.getValue().results1);

				String label = entry.getValue().label;
				if (label == null)
					label = entry.getKey().toString();
				names.add(label);
				String colour = entry.getValue().colour;
				if (colour == null) colour = defaultColour;
				colours.add(colour);
			}
			return Collections.singletonList(Mann_Whitney_U_Test(data, data1,names.size()==1?null:names,colours,
					(!xAxis.isEmpty() || !yAxis.isEmpty())?	"xlab=\""+xAxis+"\",ylab=\""+yAxis+"\""
							:null		
							));
			}

		@Override
		protected double computeHorizSize() {
			double horizSize=ySize*collectionOfResults.keySet().size()/5;if (horizSize < ySize) horizSize = ySize;
			return horizSize;
		}

		@Override
		protected Map<String , List<Double>> get_Table() {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	public static class Kruskal_Wallis<ELEM extends Comparable<? super ELEM>> extends RGraph<ELEM>
	{
		public Kruskal_Wallis(String x, String y, File name) {
			super(x, y, name);
		}
		
		@Override
		public List<String> getDrawingCommand()
		{
			List<Double> data = new LinkedList<Double>();
			List<Double> data1 = new LinkedList<Double>();

			List<String> names = new LinkedList<String>(), colours = new LinkedList<String>();
			for(Entry<ELEM, DataColumnPairValues> entry:collectionOfResults2.entrySet())
			{
				data.addAll(entry.getValue().results);
				data1.addAll(entry.getValue().results1);

				String label = entry.getValue().label;
				if (label == null)
					label = entry.getKey().toString();
				names.add(label);
				String colour = entry.getValue().colour;
				if (colour == null) colour = defaultColour;
				colours.add(colour);
			}
			return Collections.singletonList(Kruskal_Wallis_Test(data, data1,names.size()==1?null:names,colours,
					(!xAxis.isEmpty() || !yAxis.isEmpty())?	"xlab=\""+xAxis+"\",ylab=\""+yAxis+"\""
							:null		
							));
			}

		@Override
		protected double computeHorizSize() {
			double horizSize=ySize*collectionOfResults.keySet().size()/5;if (horizSize < ySize) horizSize = ySize;
			return horizSize;
		}

		@Override
		protected Map<String , List<Double>> get_Table() {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	
	public static class RBagPlot extends Graph2D
	{
		public RBagPlot(String x, String y, File name) {
			super(x, y,"bagplot", name);
		}
		/** Returns a string reflecting the number of points R bagplot analysis will be limited to. */
		protected String formatApproxLimit()
		{
			return (limit == null?"":"approx.limit="+limit.intValue());
		}
		protected Integer limit = null;

		/** By default, R's bagplot limits the number of points for analysis to 300, this one makes it possible to change that value. */
		public void setLimit(int value)
		{
			limit = value;
		}
		
		@Override
		public String otherOptions()
		{
			return formatApproxLimit();
		}
	}
	public static class Graph2D extends RGraph<Double>
	{
		public Graph2D(String x, String y, String plotKind, File name) {
			super(x, y, name);plotType=plotKind;
		}
		List<List<Double>> data = null;
		List<Double> names = null;
		
		public void computeDataSet()
		{
			data = new LinkedList<List<Double>>();
			names = new LinkedList<Double>();
			for(Entry<Double,DataColumn> entry:collectionOfResults.entrySet())
			{
				data.add(entry.getValue().results);names.add(entry.getKey());
			}
		}
		
		final protected String plotType;
		
		public String otherOptions()
		{
			return "";
		}
		
		@Override
		public List<String> getDrawingCommand()
		{
			computeDataSet();
			return Collections.singletonList(datasetToString(plotType,data, names,"xlab=\""+xAxis+"\",ylab=\""+yAxis+"\""+
					otherOptions()));
		}
		
		public boolean graphOk()
		{
			Rectangle2D.Double graphSize = getSize();
			if (graphSize.width < Configuration.fpAccuracy)
				return false;
			if (graphSize.height < Configuration.fpAccuracy)
				return false;
		
			return true;
		}
		
		/** Computes the data for abline to draw a diagonal. */
		public String computeDiagonal()
		{
			Rectangle2D.Double graphSize = getSize();
			if (graphSize.width < Configuration.fpAccuracy)
				throw new IllegalArgumentException("width is too small");
			if (graphSize.height < Configuration.fpAccuracy)
				throw new IllegalArgumentException("height is too small");
			
			double k = graphSize.height/graphSize.width;
			double diff = graphSize.y-k*graphSize.x;
			
			return "abline("+diff+","+k+")";
		}
		
		public Rectangle2D.Double getSize()
		{
			Double xValueMin = null, xValueMax = null, yValueMin = null, yValueMax = null;
			// if there is nothing useful to draw, do not pass the command to Bagplot - it will crash (as of May 24, 2011).
			Iterator<Entry<Double,DataColumn>> resultIterator = collectionOfResults.entrySet().iterator();

			while(resultIterator.hasNext())
			{
				Entry<Double,DataColumn> entry = resultIterator.next();
				if (xValueMin == null) { xValueMin = entry.getKey();xValueMax = entry.getKey(); }
				if (xValueMin.compareTo(entry.getKey()) > 0) xValueMin = entry.getKey();
				if (xValueMax.compareTo(entry.getKey()) < 0) xValueMax = entry.getKey();
				
				for(Double y:entry.getValue().results)
				{
					if (yValueMin == null) { yValueMin = y;yValueMax = y; }
					if (yValueMin.compareTo(y) > 0) yValueMin = y;
					if (yValueMax.compareTo(y) < 0) yValueMax = y;
				}
			}
			
			if (xValueMin == null || yValueMin == null)
				return new Rectangle2D.Double();
			
			return new Rectangle2D.Double(xValueMin,yValueMin,xValueMax-xValueMin,yValueMax-yValueMin);
		}
		
		@Override
		public void drawInteractive(DrawGraphs gr)
		{
			if (!checkSingleDot())
				super.drawInteractive(gr);
			else
				if (GlobalConfiguration.getConfiguration().isAssertEnabled())
					System.out.println("WARNING: not popping bagplot "+file+" consisting of a single dot due to R bug");
		}
		
		@Override
		protected double computeHorizSize() {
			return ySize;
		}

		public boolean checkSingleDot() {
			return getSize().width < Configuration.fpAccuracy && getSize().height < Configuration.fpAccuracy;
		}

		@Override
		protected Map<String , List<Double>> get_Table() {
			// TODO Auto-generated method stub
			return null;
		}
	}
	
	public static class ScatterPlot extends Graph2D
	{

		public ScatterPlot(String x, String y, File name) {
			super(x, y, "plot", name);
		}
		
	}
	
	/** Draws a square bag plot. */
	public static class SquareBagPlot extends RBagPlot
	{
		protected final boolean diag;
		protected final double minValue, maxValue;
		/**
		 * 
		 * @param x name of the X axis
		 * @param y name of the Y axis
		 * @param name file where to store .pdf (should include the extension).
		 * @param from the minimal value of x or y.
		 * @param to the maximal value of x or y.
		 * @param diagonal whether to draw a diagonal line
		 */
		public SquareBagPlot(String x, String y, File name, double from, double to, boolean diagonal) {
			super(x, y, name);diag = diagonal;minValue = from;maxValue = to;
		}
		
		@Override
		public List<String> getDrawingCommand()
		{
			computeDataSet();
			List<String> result = new LinkedList<String>();
			result.add("bplot<-compute."+datasetToString(plotType,data, names,formatApproxLimit()));
			result.add("plot(bplot,xlim=c("+minValue+","+maxValue+"), ylim=c("+minValue+","+maxValue+"),xlab=\""+xAxis+"\",ylab=\""+yAxis+"\")");
			if (diag) result.add("abline(0,1)");
			return result;
		}
	}
	
	/**
	 * A version DataColoumn method that allow the user to store two results in a MAP <ELEM,DataColumnPairValues>();
	 *  where DataColumnPairValues has pair of value to add each time
	 */
	public static class StatsticatTestResult
	{
		/** Data to be displayed. */
		double statistic;
		double pvalue;
		String alternative; 
		String Method;
		double parameter;

		public StatsticatTestResult()
		{
			statistic = 0.0; 
			pvalue = 0.0;
		}
		public double getStatistic()
      {
    	  return statistic;
      }
		public  double getPvalue()
      {
    	  return pvalue;
      }
		public String getAlternative()
      {
    	  return alternative;
      }
	  public String getMethod()
	  {
		  return Method;
	  }
	  public double getParameter()
	  {
		  return parameter;
	  }
	}

	public void writetofile(List<String> drawingCommands, DrawGraphs gr, File file) {
		
		StatsticatTestResult o=CollectResultStatsticalResult(drawingCommands);
		try
		{
			String Filename = file.getName();
			FileWriter writer = new FileWriter(Filename);	    
		    writer.append("Method");
		    writer.append(',');
		    writer.append("Alternative");
		    writer.append(',');
		    writer.append("P-value");
		    writer.append(',');
		    if(o.getMethod().equals("Wilcoxon signed rank test"))
		    {
		    	writer.append("V");
		    }
		    if(o.getMethod().equals("Wilcoxon rank sum test"))
		    {
			    writer.append("W");
		    }
		    if(o.getMethod().equals("Kruskal-Wallis rank sum test"))
		    {
			    writer.append("Kruskal-Wallis chi-squared ");
		    	writer.append(',');
		    	writer.append("df");
		    }

		    
		    writer.append('\n');
 
		    writer.append(String.valueOf(o.getMethod()));
		    writer.append(',');
		    writer.append(String.valueOf(o.getStatistic()));
		    writer.append(',');
		    writer.append(String.valueOf(o.getPvalue()));
		    writer.append(',');
		    writer.append(String.valueOf(o.getStatistic()));
		    if(o.getMethod().equals("Kruskal-Wallis rank sum test"))
		    {
		    	writer.append(',');		    
		    	writer.append(String.valueOf(o.getParameter()));
		    }
	            writer.append('\n');
 

 
		    //generate whatever data you want
	 
		    writer.flush();
		    writer.close();
		}
		catch(IOException e)
		{
			e.printStackTrace();
		} 
	}
	
	public void writingExcelFile(Map<String , List<Double>> list, DrawGraphs gr, File file) 
	{
		try
		{
			String Filename = file.getName();
			FileWriter writer = new FileWriter(Filename);
			writer.append("States");
			writer.append(',');
		    writer.append("NumberofQuestion");
		    writer.append('\n');
			for(String e:list.keySet())
			{
				for(Double r:list.get(e))
				{
					writer.append(e);
					writer.append(',');
				    writer.append(r.toString());
				    writer.append('\n');				
				}
			}
		
			writer.flush();
		    writer.close();
		}
		catch(IOException e)
		{
			e.printStackTrace();
		} 
	}

	public static class RecordingQuestion
	{
		public double actualElem, RefercneElem;
		public RecordingQuestion(double a, double b) {
			actualElem=a;RefercneElem=b;
		}
		
		
		@Override
		public String toString()
		{
			return "(Actual: "+actualElem+", Reference: "+RefercneElem+")";
		}
	}
}

