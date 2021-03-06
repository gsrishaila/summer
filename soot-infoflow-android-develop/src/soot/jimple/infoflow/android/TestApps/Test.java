/*******************************************************************************
 * Copyright (c) 2012 Secure Software Engineering Group at EC SPRIDE.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser Public License v2.1
 * which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/old-licenses/gpl-2.0.html
 * 
 * Contributors: Christian Fritz, Steven Arzt, Siegfried Rasthofer, Eric
 * Bodden, and others.
 ******************************************************************************/
package soot.jimple.infoflow.android.TestApps;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import javax.xml.stream.XMLStreamException;

import org.xmlpull.v1.XmlPullParserException;

import soot.Body;
import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.PatchingChain;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.InvokeExpr;
import soot.jimple.Jimple;
import soot.jimple.Stmt;
import soot.jimple.infoflow.InfoflowConfiguration.AliasingAlgorithm;
import soot.jimple.infoflow.InfoflowConfiguration.CallgraphAlgorithm;
import soot.jimple.infoflow.InfoflowConfiguration.CodeEliminationMode;
import soot.jimple.infoflow.InfoflowConfiguration.DataFlowSolver;
import soot.jimple.infoflow.InfoflowManager;
import soot.jimple.infoflow.android.InfoflowAndroidConfiguration;
import soot.jimple.infoflow.android.InfoflowAndroidConfiguration.CallbackAnalyzer;
import soot.jimple.infoflow.android.SetupApplication;
import soot.jimple.infoflow.android.source.AndroidSourceSinkManager.LayoutMatchingMode;
import soot.jimple.infoflow.config.IInfoflowConfig;
import soot.jimple.infoflow.data.Abstraction;
import soot.jimple.infoflow.data.pathBuilders.DefaultPathBuilderFactory.PathBuilder;
import soot.jimple.infoflow.handlers.ResultsAvailableHandler;
import soot.jimple.infoflow.ipc.IIPCManager;
import soot.jimple.infoflow.results.InfoflowResults;
import soot.jimple.infoflow.results.ResultSinkInfo;
import soot.jimple.infoflow.results.ResultSourceInfo;
import soot.jimple.infoflow.results.xml.InfoflowResultsSerializer;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;
import soot.jimple.infoflow.taintWrappers.ITaintPropagationWrapper;
import soot.jimple.infoflow.util.SystemClassHandler;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.options.Options;
import soot.tagkit.StringTag;
import soot.tagkit.Tag;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.BlockGraph;
import soot.toolkits.graph.BriefBlockGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.UnitGraph;
import soot.util.dot.DotGraph;
import soot.util.queue.QueueReader;
//***
import soot.util.cfgcmd.CFGToDotGraph;
import soot.util.dot.DotGraph;

public class Test {
	
	private static final class MyResultsAvailableHandler implements
			ResultsAvailableHandler {
		private final BufferedWriter wr;

		private MyResultsAvailableHandler() {
			this.wr = null;
		}

		private MyResultsAvailableHandler(BufferedWriter wr) {
			this.wr = wr;
		}

		@Override
		public void onResultsAvailable(
				IInfoflowCFG cfg, InfoflowResults results) {
			// Dump the results
			if (results == null) {
				print("No results found.");
			}
			else {
				// Report the results
				for (ResultSinkInfo sink : results.getResults().keySet()) {
					if (config.isIccEnabled() && config.isIccResultsPurifyEnabled()) {
						print("Found an ICC flow to sink " + sink + ", from the following sources:");
					}
					else {
						print("Found a flow to sink " + sink + ", from the following sources:");
					}
					
					for (ResultSourceInfo source : results.getResults().get(sink)) {
						print("\t- " + source.getSource() + " (in "
								+ cfg.getMethodOf(source.getSource()).getSignature()  + ")");
						if (source.getPath() != null)
							print("\t\ton Path " + Arrays.toString(source.getPath()));
					}
				}
				
				// Serialize the results if requested
				// Write the results into a file if requested
				if (resultFilePath != null && !resultFilePath.isEmpty()) {
					InfoflowResultsSerializer serializer = new InfoflowResultsSerializer(cfg, config);
					try {
						serializer.serialize(results, resultFilePath);
					} catch (FileNotFoundException ex) {
						System.err.println("Could not write data flow results to file: " + ex.getMessage());
						ex.printStackTrace();
						throw new RuntimeException(ex);
					} catch (XMLStreamException ex) {
						System.err.println("Could not write data flow results to file: " + ex.getMessage());
						ex.printStackTrace();
						throw new RuntimeException(ex);
					}
				}
			}
			
		}

		private void print(String string) {
			try {
				System.out.println(string);
				if (wr != null)
					wr.write(string + "\n");
			}
			catch (IOException ex) {
				// ignore
			}
		}
	}
	
	private static InfoflowAndroidConfiguration config = new InfoflowAndroidConfiguration();
	
	private static int repeatCount = 1;
	private static int timeout = -1;
	private static int sysTimeout = -1;
	//Added in for testing
	static int noOfLoops=0;
	static int tailCnt=0,headCnt=0;
	//Added in for testing
	
	private static boolean aggressiveTaintWrapper = false;
	private static boolean noTaintWrapper = false;
	private static String summaryPath = "";
	private static String resultFilePath = "";
	
	//create a list of the soot methods name
	static List<String> sootMethodsNameList = new ArrayList<String>();
	static List<String> sootMethodsSignatureList = new ArrayList<String>();
	static List<String> sootMethodsSubSignatureList = new ArrayList<String>();
	static List<SootMethod> sootMethodsObjectList = new ArrayList<SootMethod>();
	
	static List<SootMethod> mergedMethodsList = new ArrayList<SootMethod>();
	static int currNoUnits=0;
	
	static HashMap<SootMethod,Queue<SootMethod>> subFunctions = new HashMap<SootMethod,Queue<SootMethod>>();
	private static IIPCManager ipcManager = null;
	public static void setIPCManager(IIPCManager ipcManager)
	{
		Test.ipcManager = ipcManager;
	}
	public static IIPCManager getIPCManager()
	{
		return Test.ipcManager;
	}
	
	//added in function
	public static File serializeCallGraph(CallGraph graph, String fileName) {
		if (fileName == null) {
			fileName = soot.SourceLocator.v().getOutputDir();
			if (fileName.length() > 0) {
				fileName = fileName + java.io.File.separator;
			}
			fileName = fileName + "call-graph" + DotGraph.DOT_EXTENSION;
		}
		DotGraph canvas = new DotGraph("call-graph");
		QueueReader<Edge> listener = graph.listener();
		while (listener.hasNext()) {
			Edge next = listener.next();
			MethodOrMethodContext src = next.getSrc();
			MethodOrMethodContext tgt = next.getTgt();
			canvas.drawNode(src.toString());
			canvas.drawNode(tgt.toString());
			canvas.drawEdge(src.toString(), tgt.toString());
		}
		canvas.plot(fileName);
		return new File(fileName);
	}
	 
	//Function added in to generate the CFG
	public static void generateCFG (SootMethod entryPoint)
	{
		System.out.println("***CFG Generation***" + entryPoint.getName());
		System.out.println("Method Sig : " + entryPoint.getSignature());
		//if(entryPoint.getSignature().equals("<com.android.insecurebank.PostLogin: void dotransfer()>"))
			//return;
		Body b = entryPoint.retrieveActiveBody();
		
		BlockGraph bg = new BriefBlockGraph(b);
		
		MHGDominatorsFinder<Block> domFinder = new MHGDominatorsFinder(bg); 
		//print basic block info 
		for (Block block:bg){
			System.out.println("\n"+block.toString());
		}//end for 
		
		BlockGraph bg1 = new BriefBlockGraph(entryPoint.getActiveBody());
		CFGToDotGraph y = new CFGToDotGraph();
	    DotGraph a1=y.drawCFG(bg,entryPoint.getActiveBody());
	    a1.plot(entryPoint.getSignature() +"333.dot");
	    
		System.out.println("***End of CFG Generation***" + entryPoint.getName()+"\n");
	}

	public static SootMethod mergeCFG1021s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList, String mainMdtName)
	{
		List<Unit> tailList = new ArrayList();
		Body body = null ;
		SootMethod dummyMainMdt = null ;
		
		int noMdtsMerged =0;
		//first get the dummy main mdt and its body
		for (SootMethod eachMdt:entryPoint)
		{
			if (eachMdt.getName().contains(mainMdtName) )
			{
				body = eachMdt.retrieveActiveBody();
				dummyMainMdt = eachMdt;//dummyMainMdt refer to the mainMdtName
			}
		}
		
		for (SootMethod eachMdt:entryPoint)
		{
			//get the units frm dummy method
			PatchingChain<Unit> unitsInDummyMdt = body.getUnits(); //unitsInDummyMdt refer to the mainMdtName
			//get the dummymainmdt
			if (eachMdt.getSignature() == mainMdtName )
				continue;
			if(unitsInDummyMdt == null)
			{
				System.out.println("unitsInDummyMdt is null");
			}
			else
			{
				System.out.println("ToMerge : "+eachMdt.getSignature());		
				for (Unit unitFrmMdt:unitsInDummyMdt)
				{	
					Stmt stmt = (Stmt)unitFrmMdt ;
					if (stmt.containsInvokeExpr()) 
					{
						 InvokeExpr invokeExpr1 = stmt.getInvokeExpr();
						 if (unitFrmMdt.toString().contains(eachMdt.getSignature()))
						 {
							 Unit successor = body.getUnits().getSuccOf(unitFrmMdt);
							 body.getUnits().getSuccOf(unitFrmMdt).addTag(new StringTag("successor"));
							 List<Unit> nonRetUnits = new ArrayList();
							 
							 InvokeExpr invokeExpr = stmt.getInvokeExpr();
				             eachMdt = invokeExpr.getMethod();
				             if(!eachMdt.hasActiveBody())
				            	 continue;
	
				             Stmt nop1=Jimple.v().newNopStmt();
							 //*****get the other tails*****
							 Unit b4Tail = null;
							 UnitGraph newone= new ExceptionalUnitGraph (eachMdt.getActiveBody());
							 
							 //only if there are other tails
							 int remainingTails=0;
							 Stmt nop=Jimple.v().newNopStmt();
						
							 Unit cloneNexUnit = (Unit) nop.clone();
							 List<Unit> clonedTailList = new ArrayList();
							 
							 nop1.addTag(new StringTag("tail"));
							
							 Unit firstTail = newone.getTails().get(0);
							
							 eachMdt.retrieveActiveBody().getUnits().swapWith(firstTail, nop1);
							 
						
							 newone.getTails().remove(0);
							 remainingTails = newone.getTails().size();
							 if(remainingTails>0)
							 {
								 for (Unit eachTailUnit:newone.getTails())
								 {
									 
									 cloneNexUnit = (Unit) nop.clone();
									 cloneNexUnit.addTag(new StringTag("tail"));
									 clonedTailList.add(cloneNexUnit);
									 tailList.add(eachTailUnit);
									 System.out.println("eachTailUnit : "+eachTailUnit.toString());
									 b4Tail =newone.getBody().getUnits().getPredOf(eachTailUnit);
									 System.out.println("b4Tail.toString() : "+b4Tail.toString());
									 newone.getBody().getUnits().swapWith(eachTailUnit, cloneNexUnit);
								 }
							 }
							//*****get the other tails*****
							//System.out.println("eachMdt unit size: "+eachMdt.retrieveActiveBody().getUnits().size());
							 body.getUnits().insertOnEdge(eachMdt.retrieveActiveBody().getUnits(),unitFrmMdt, successor);
							
							 if(remainingTails>0)
							 {
								 for (Unit clonedRet:clonedTailList)
								 {
									 body.getUnits().remove(successor);
									 System.out.println("successor: "+successor.toString());
									 System.out.println("clonedRet: "+clonedRet.toString());
									 body.getUnits().insertAfter(successor,clonedRet); //added in *****get the other tails***** 
								 } 
							 }
							 
							 Body b = body;
						     BlockGraph bg = new BriefBlockGraph(b);//this line is needed to remove the duplicate block
						     
						     PatchingChain<Unit> unitsInDummyMdt1 = body.getUnits();
							 noMdtsMerged++;
							 mergedMethodsList.add(eachMdt);
							 CFGToDotGraph y = new CFGToDotGraph();
							 DotGraph a1=y.drawCFG(bg,b);
							 if(eachMdt.getSignature().toString().equals("<com.example.gsrishaila.myapplication.MainActivity: boolean onOptionsItemSelected(android.view.MenuItem)>"))
								 a1.plot("dummymain" +"334.dot"); 
							 a1.plot("dummymain" +"333.dot");
							//***clear all the tags***
							 Tag tagVal1;
						     for (Unit eachUnit:unitsInDummyMdt1)
						     {
						    	 if(eachUnit.getTags().size()>0)
						    	 {
						    			 tagVal1 = eachUnit.getTags().get(eachUnit.getTags().size()-1);
						    			 if(tagVal1.toString() =="tail")
						    			 {
						    				 eachUnit.getTags().remove(eachUnit.getTags().size()-1);
						    				 String tailString = "oldtail_"+ tailCnt;
						    				 eachUnit.addTag(new StringTag(tailString)); 
						    			 }
						    			 if(tagVal1.toString() =="successor")
						    			 {
						    				 eachUnit.getTags().remove(eachUnit.getTags().size()-1);
						    				 System.out.println("successor removed!!!");
						    				 String successorString = "oldsuccessor_"+ tailCnt;
						    				 eachUnit.addTag(new StringTag(successorString));
						    				 tailCnt++;
						    			 }
						    	 }
						     }
						    	 BlockGraph bg1 = new BriefBlockGraph(b);
						    	 for (Block block:bg1)
								 {
									System.out.println("\n"+block.toString());
								 }
						    	 CFGToDotGraph y1 = new CFGToDotGraph();
								 DotGraph a11=y.drawCFG(bg1,b);
								 if(eachMdt.getSignature().toString().equals("<com.example.gsrishaila.myapplication.MainActivity: boolean onOptionsItemSelected(android.view.MenuItem)>"))
									 a11.plot("dummymain" +"334.dot"); 
								 a11.plot("dummymain" +"333.dot");
							 
							 currNoUnits = body.getUnits().size(); //update global units count for recursive while loop	 
						     break;
						 }//remove if
					}
					
				}//eachmdtloop
			}
		}
		//******
		BlockGraph bg1 = new BriefBlockGraph(body);
		for (Block block:bg1)
		 {
			System.out.println("\n"+block.toString());
		 }
		CFGToDotGraph y = new CFGToDotGraph();
		DotGraph a1=y.drawCFG(bg1,body); 
		a1.plot("dummymain" +"335.dot");
		//******
		
		return dummyMainMdt;
	}
	
	/**
	 * @param args Program arguments. args[0] = path to apk-file,
	 * args[1] = path to android-dir (path/android-platforms/)
	 */
	public static void main(final String[] args) throws IOException, InterruptedException {
		if (args.length < 2) {
			printUsage();	
			return;
		}
		//start with cleanup:
		File outputDir = new File("JimpleOutput");
		if (outputDir.isDirectory()){
			boolean success = true;
			for(File f : outputDir.listFiles()){
				success = success && f.delete();
			}
			if(!success){
				System.err.println("Cleanup of output directory "+ outputDir + " failed!");
			}
			outputDir.delete();
		}
		
		// Parse additional command-line arguments
		if (!parseAdditionalOptions(args))
			return;
		if (!validateAdditionalOptions())
			return;
		if (repeatCount <= 0)
			return;
		
		List<String> apkFiles = new ArrayList<String>();
		File apkFile = new File(args[0]);
		if (apkFile.isDirectory()) {
			String[] dirFiles = apkFile.list(new FilenameFilter() {
			
				@Override
				public boolean accept(File dir, String name) {
					return (name.endsWith(".apk"));
				}
			
			});
			for (String s : dirFiles)
				apkFiles.add(s);
		} else {
			//apk is a file so grab the extension
			String extension = apkFile.getName().substring(apkFile.getName().lastIndexOf("."));
			if (extension.equalsIgnoreCase(".txt")) {
				BufferedReader rdr = new BufferedReader(new FileReader(apkFile));
				String line = null;
				while ((line = rdr.readLine()) != null)
					apkFiles.add(line);
				rdr.close();
			}
			else if (extension.equalsIgnoreCase(".apk"))
				apkFiles.add(args[0]);
			else {
				System.err.println("Invalid input file format: " + extension);
				return;
			}
		}
		
		int oldRepeatCount = repeatCount;
		for (final String fileName : apkFiles) {
			repeatCount = oldRepeatCount;
			final String fullFilePath;
			System.gc();
			
			// Directory handling
			if (apkFiles.size() > 1) {
				if (apkFile.isDirectory())
					fullFilePath = args[0] + File.separator + fileName;
				else
					fullFilePath = fileName;
				System.out.println("Analyzing file " + fullFilePath + "...");
				File flagFile = new File("_Run_" + new File(fileName).getName());
				if (flagFile.exists())
					continue;
				flagFile.createNewFile();
			}
			else
				fullFilePath = fileName;

			// Run the analysis
			while (repeatCount > 0) {
				System.gc();
				if (timeout > 0)
					runAnalysisTimeout(fullFilePath, args[1]);
				else if (sysTimeout > 0)
					runAnalysisSysTimeout(fullFilePath, args[1]);
				else
					runAnalysis(fullFilePath, args[1]);
				repeatCount--;
			}
			
			System.gc();
		}
		
	   //*****added in code2*****
	   PrintStream out = new PrintStream(new FileOutputStream("output.txt"));
	   System.setOut(out);
	   String androidPlatformPath = "/home/shaila/Android/Sdk/platforms";
	   
	   //String appPath = "/home/shaila/Desktop/NewAPKs2/Broadcast/BroadcastReceiver/OriginalAPK/BroadcastReceiverNewSms-debug.apk";
	   String appPath = "/home/shaila/Desktop/NewAPKs2/ServiceComponent/OriginalAPK/ServiceOriginalApk.apk";
	   //String appPath = "/home/shaila/Desktop/MyDPT12.apk";
	   SetupApplication app = new SetupApplication
	                (androidPlatformPath,
	                        appPath);
	   //app.calculateSourcesSinksEntrypoints("D:\\Arbeit\\Android Analyse\\soot-infoflow-android\\SourcesAndSinks.txt");
	   //app.calculateSourcesSinksEntrypoints("/home/shaila/Desktop/flowdroid2/soot-infoflow-android-develop/SourcesAndSinks.txt");
       try {
		app.runInfoflow("/home/shaila/Desktop/flowdroid2/soot-infoflow-android-develop/SourcesAndSinks.txt");
	} catch (XmlPullParserException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	}
	        soot.G.reset();
       Options.v().set_src_prec(Options.src_prec_apk);
	   Options.v().set_process_dir(Collections.singletonList(appPath));
	   Options.v().set_android_jars(androidPlatformPath);
	   Options.v().set_whole_program(true);
	   Options.v().set_allow_phantom_refs(true);
	   Options.v().setPhaseOption("cg.spark", "on");

	   Scene.v().loadNecessaryClasses();
	   
	   //SootMethod entryPoint = app.getEntryPointCreator().createDummyMain();
	   SootMethod entryPoint = app.getDummyMainMethod();
	   BlockGraph bg1 = new BriefBlockGraph(entryPoint.getActiveBody());
	   CFGToDotGraph y = new CFGToDotGraph();
	   DotGraph a1=y.drawCFG(bg1,entryPoint.getActiveBody());
	   a1.plot("original_dummymain");
	   sootMethodsObjectList.add(entryPoint);
	   Options.v().set_main_class(entryPoint.getSignature());
	   Scene.v().setEntryPoints(Collections.singletonList(entryPoint));
	   
	   PackManager.v().getPack("cg").apply(); //this works
	   CallGraph appCallGraph = Scene.v().getCallGraph();
	   File graph =serializeCallGraph(appCallGraph, "callgraph");
	   
	   System.out.println(entryPoint.getActiveBody());
	    
	    //getting the CFG of the DummyMainMethod
	    generateCFG (entryPoint);
	    
	    //getting the entrypoint classes from the DummyMainMethod
	    Set <SootClass> entryPoint1 =  app.getEntrypointClasses();
	    System.out.println(entryPoint1);
	    
	    PatchingChain<Unit> unitsInDummyMdt = entryPoint.retrieveActiveBody().getUnits(); //unitsInDummyMdt refer to the mainMdtName
        Queue<SootMethod> newMdtQueue = new LinkedList<SootMethod>();
		for (Unit unitInMdt:unitsInDummyMdt)
		{
			Stmt stmt = (Stmt)unitInMdt ;
			if (stmt != null) 
			{
	            if (stmt.containsInvokeExpr()) 
	            {
	                InvokeExpr invokeExpr = stmt.getInvokeExpr();
	                SootMethod method = invokeExpr.getMethod();
	                method.getActiveBody();
	                newMdtQueue.add(method); 
	            }
			}
		}//end of for loop
	    //Find all the methods called in the dummymain mdt
	    //findFunctionsToMerge (newMdtQueue, entryPoint);
	    for (Entry<SootMethod, Queue<SootMethod>> entry : subFunctions.entrySet())
	    {
	    	 SootMethod key = entry.getKey();
	    	 Queue<SootMethod> value = entry.getValue(); 
	    	 System.out.println("key: "+key.getSignature());
	    	 for (SootMethod frmQ:value)
	    	 {
	    		 System.out.println("Value: "+frmQ.getSignature());
	    	 } 
	    }
	    //***
	    
	    //original while loop
	    //***Adding all methods to sootMethodsObjectList 
	    int origNoUnits = unitsInDummyMdt.size();
	    while (true)
	    {
	    origNoUnits = unitsInDummyMdt.size(); //get initial number of units
	    
	    System.out.println("origNoUnits: "+origNoUnits);
	    for (Unit unitInMdt:unitsInDummyMdt)
		{
			Stmt stmt = (Stmt)unitInMdt ;
			if (stmt != null) 
			{
	            if (stmt.containsInvokeExpr()) 
	            {
	                InvokeExpr invokeExpr = stmt.getInvokeExpr();
	                SootMethod method = invokeExpr.getMethod();
					
	                if(mergedMethodsList.contains(method))
	                {
	                	continue;
	                }
	                if(method.hasActiveBody())
	                {
	                	if(!sootMethodsObjectList.contains(method))
	                	{
	                		sootMethodsObjectList.add(method);
	                		sootMethodsSignatureList.add(method.getSignature());
	                		generateCFG (method);
	                	}
	                } 
	            }
			}
		}//end of for loop
	    //***Adding all methods to sootMethodsObjectList 
	    System.out.println("calling the mergeCFG1021s method...\n");
	    SootMethod newOne=mergeCFG1021s (sootMethodsObjectList, sootMethodsSignatureList,"dummyMainMethod");
	    unitsInDummyMdt = newOne.getActiveBody().getUnits();
	    /*for (SootMethod mdtInList:sootMethodsObjectList)
	    {
	    	System.out.println("mdtInList: " + mdtInList);
	    }*/
	    //print currNoUnits
	    System.out.println("origNoUnits: "+origNoUnits);
	    System.out.println("currNoUnits: " + currNoUnits);
	    System.out.println("newOne.noUnits: " +newOne.getActiveBody().getUnits().size() ); //seems updated
	    if(currNoUnits==origNoUnits)
	    	break;
	    sootMethodsObjectList.clear();
	    sootMethodsObjectList.add(entryPoint); //add the dummymain mdt
		sootMethodsSignatureList.clear();
		noOfLoops++;
		//if(noOfLoops==2)
			//break;
	    //break;//for test
		
	    }//end of while
	    //original while loop	    
	    System.out.println("sootMethodsObjectList: " + sootMethodsObjectList);
	    System.out.println("sootMethodsNameList: " + sootMethodsNameList);
	    System.out.println("sootMethodsSignatureList: " + sootMethodsSignatureList);
	   //*****added in code2*****
      
	}

	/**
	 * Parses the optional command-line arguments
	 * @param args The array of arguments to parse
	 * @return True if all arguments are valid and could be parsed, otherwise
	 * false
	 */
	@SuppressWarnings("deprecation")
	private static boolean parseAdditionalOptions(String[] args) {
		int i = 2;
		while (i < args.length) {
			if (args[i].equalsIgnoreCase("--timeout")) {
				int realTimeout = Integer.valueOf(args[i+1]);
				timeout = realTimeout + 1;
				config.setDataFlowTimeout(realTimeout);
				i += 2;
			}

			else if (args[i].equalsIgnoreCase("--callbacktimeout")) {
				int realTimeout = Integer.valueOf(args[i+1]);
				timeout = realTimeout + 1;
				config.setCallbackAnalysisTimeout(realTimeout);
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--resulttimeout")) {
				int realTimeout = Integer.valueOf(args[i+1]);
				timeout = realTimeout + 1;
				config.setResultSerializationTimeout(realTimeout);
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--systimeout")) {
				sysTimeout = Integer.valueOf(args[i+1]);
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--singleflow")) {
				config.setStopAfterFirstFlow(true);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--implicit")) {
				config.setEnableImplicitFlows(true);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--nostatic")) {
				config.setEnableStaticFieldTracking(false);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--aplength")) {
				config.setAccessPathLength(Integer.valueOf(args[i+1]));
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--cgalgo")) {
				String algo = args[i+1];
				if (algo.equalsIgnoreCase("AUTO"))
					config.setCallgraphAlgorithm(CallgraphAlgorithm.AutomaticSelection);
				else if (algo.equalsIgnoreCase("CHA"))
					config.setCallgraphAlgorithm(CallgraphAlgorithm.CHA);
				else if (algo.equalsIgnoreCase("VTA"))
					config.setCallgraphAlgorithm(CallgraphAlgorithm.VTA);
				else if (algo.equalsIgnoreCase("RTA"))
					config.setCallgraphAlgorithm(CallgraphAlgorithm.RTA);
				else if (algo.equalsIgnoreCase("SPARK"))
					config.setCallgraphAlgorithm(CallgraphAlgorithm.SPARK);
				else if (algo.equalsIgnoreCase("GEOM"))
					config.setCallgraphAlgorithm(CallgraphAlgorithm.GEOM);
				else {
					System.err.println("Invalid callgraph algorithm");
					return false;
				}
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--nocallbacks")) {
				config.setEnableCallbacks(false);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--noexceptions")) {
				config.setEnableExceptionTracking(false);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--layoutmode")) {
				String algo = args[i+1];
				if (algo.equalsIgnoreCase("NONE"))
					config.setLayoutMatchingMode(LayoutMatchingMode.NoMatch);
				else if (algo.equalsIgnoreCase("PWD"))
					config.setLayoutMatchingMode(LayoutMatchingMode.MatchSensitiveOnly);
				else if (algo.equalsIgnoreCase("ALL"))
					config.setLayoutMatchingMode(LayoutMatchingMode.MatchAll);
				else {
					System.err.println("Invalid layout matching mode");
					return false;
				}
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--aliasflowins")) {
				config.setFlowSensitiveAliasing(false);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--paths")) {
				config.setComputeResultPaths(true);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--nopaths")) {
				config.setComputeResultPaths(false);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--aggressivetw")) {
				aggressiveTaintWrapper = false;
				i++;
			}
			else if (args[i].equalsIgnoreCase("--pathalgo")) {
				String algo = args[i+1];
				if (algo.equalsIgnoreCase("CONTEXTSENSITIVE"))
					config.setPathBuilder(PathBuilder.ContextSensitive);
				else if (algo.equalsIgnoreCase("CONTEXTINSENSITIVE"))
					config.setPathBuilder(PathBuilder.ContextInsensitive);
				else if (algo.equalsIgnoreCase("SOURCESONLY"))
					config.setPathBuilder(PathBuilder.ContextInsensitiveSourceFinder);
				else {
					System.err.println("Invalid path reconstruction algorithm");
					return false;
				}
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--summarypath")) {
				summaryPath = args[i + 1];
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--saveresults")) {
				resultFilePath = args[i + 1];
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--sysflows")) {
				config.setIgnoreFlowsInSystemPackages(false);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--notaintwrapper")) {
				noTaintWrapper = true;
				i++;
			}
			else if (args[i].equalsIgnoreCase("--notypechecking")) {
				config.setEnableTypeChecking(false);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--repeatcount")) {
				repeatCount = Integer.parseInt(args[i + 1]);
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--noarraysize")) {
				config.setEnableArraySizeTainting(false);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--arraysize")) {
				config.setEnableArraySizeTainting(true);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--safemode")) {
				config.setUseThisChainReduction(false);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--logsourcesandsinks")) {
				config.setLogSourcesAndSinks(true);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--callbackanalyzer")) {
				String algo = args[i+1];
				if (algo.equalsIgnoreCase("DEFAULT"))
					config.setCallbackAnalyzer(CallbackAnalyzer.Default);
				else if (algo.equalsIgnoreCase("FAST"))
					config.setCallbackAnalyzer(CallbackAnalyzer.Fast);
				else {
					System.err.println("Invalid callback analysis algorithm");
					return false;
				}
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--maxthreadnum")){
				config.setMaxThreadNum(Integer.valueOf(args[i+1]));
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--arraysizetainting")) {
				config.setEnableArraySizeTainting(true);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--dataflowsolver")) {
				String algo = args[i+1];
				if (algo.equalsIgnoreCase("HEROS"))
					config.setDataFlowSolver(DataFlowSolver.Heros);
				else if (algo.equalsIgnoreCase("CONTEXTFLOWSENSITIVE"))
					config.setDataFlowSolver(DataFlowSolver.ContextFlowSensitive);
				else if (algo.equalsIgnoreCase("FLOWINSENSITIVE"))
					config.setDataFlowSolver(DataFlowSolver.FlowInsensitive);
				else {
					System.err.println("Invalid data flow algorithm");
					return false;
				}
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--iccmodel")) {
				config.setIccModel(args[i+1]);
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--noiccresultspurify")) {
				config.setIccResultsPurify(false);
				i++;
			}


			else if (args[i].equalsIgnoreCase("--onecomponentatatime")) {
				config.setOneComponentAtATime(true);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--onesourceatatime")) {
				config.setOneSourceAtATime(true);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--aliasalgo")) {
				String algo = args[i+1];
				if (algo.equalsIgnoreCase("NONE"))
					config.setAliasingAlgorithm(AliasingAlgorithm.None);
				else if (algo.equalsIgnoreCase("FLOWSENSITIVE"))
					config.setAliasingAlgorithm(AliasingAlgorithm.FlowSensitive);
				else if (algo.equalsIgnoreCase("PTSBASED"))
					config.setAliasingAlgorithm(AliasingAlgorithm.PtsBased);
				else if (algo.equalsIgnoreCase("LAZY"))
					config.setAliasingAlgorithm(AliasingAlgorithm.Lazy);
				else {
					System.err.println("Invalid aliasing algorithm");
					return false;
				}
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--codeelimination")) {
				String algo = args[i+1];
				if (algo.equalsIgnoreCase("NONE"))
					config.setCodeEliminationMode(CodeEliminationMode.NoCodeElimination);
				else if (algo.equalsIgnoreCase("PROPAGATECONSTS"))
					config.setCodeEliminationMode(CodeEliminationMode.PropagateConstants);
				else if (algo.equalsIgnoreCase("REMOVECODE"))
					config.setCodeEliminationMode(CodeEliminationMode.RemoveSideEffectFreeCode);
				else {
					System.err.println("Invalid code elimination mode");
					return false;
				}
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--enablereflection")) {
				config.setEnableRefection(true);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--sequentialpathprocessing")) {
				config.setSequentialPathProcessing(true);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--singlejoinpointabstraction")) {
				config.setSingleJoinPointAbstraction(true);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--nocallbacksources")) {
				config.setEnableCallbackSources(false);
				i++;
			}
			else if (args[i].equalsIgnoreCase("--maxcallbackspercomponent")) {
				config.setMaxCallbacksPerComponent(Integer.valueOf(args[i+1]));
				i += 2;
			}
			else if (args[i].equalsIgnoreCase("--incrementalresults")) {
				config.setIncrementalResultReporting(true);
				i++;
			}
			else
				i++;
		}
		return true;
	}
	
	private static boolean validateAdditionalOptions() {
		if (timeout > 0 && sysTimeout > 0) {
			return false;
		}
		if (!config.getFlowSensitiveAliasing()
				&& config.getAliasingAlgorithm() != AliasingAlgorithm.FlowSensitive) {
			System.err.println("Flow-insensitive aliasing can only be configured for callgraph "
					+ "algorithms that support this choice.");
			return false;
		}
		return true;
	}
	
	private static void runAnalysisTimeout(final String fileName, final String androidJar) {
		FutureTask<InfoflowResults> task = new FutureTask<InfoflowResults>(new Callable<InfoflowResults>() {

			@Override
			public InfoflowResults call() throws Exception {
				
				final BufferedWriter wr = new BufferedWriter(new FileWriter("_out_" + new File(fileName).getName() + ".txt"));
				try {
					final long beforeRun = System.nanoTime();
					wr.write("Running data flow analysis...\n");
					final InfoflowResults res = runAnalysis(fileName, androidJar);
					wr.write("Analysis has run for " + (System.nanoTime() - beforeRun) / 1E9 + " seconds\n");
					
					wr.flush();
					return res;
				}
				finally {
					if (wr != null)
						wr.close();
				}
			}
			
		});
		ExecutorService executor = Executors.newFixedThreadPool(1);
		executor.execute(task);
		
		try {
			System.out.println("Running infoflow task...");
			task.get(timeout, TimeUnit.SECONDS);
		} catch (ExecutionException e) {
			System.err.println("Infoflow computation failed: " + e.getMessage());
			e.printStackTrace();
		} catch (TimeoutException e) {
			// This is expected, do not report it
		} catch (InterruptedException e) {
			System.err.println("Infoflow computation interrupted: " + e.getMessage());
			e.printStackTrace();
		}
		
		// Make sure to remove leftovers
		executor.shutdown();		
	}

	private static void runAnalysisSysTimeout(final String fileName, final String androidJar) {
		String classpath = System.getProperty("java.class.path");
		String javaHome = System.getProperty("java.home");
		String executable = "/usr/bin/timeout";
		String[] command = new String[] { executable,
				"-s", "KILL",
				sysTimeout + "s",
				javaHome + "/bin/java",
				"-cp", classpath,
				"soot.jimple.infoflow.android.TestApps.Test",
				fileName,
				androidJar,
				config.getStopAfterFirstFlow() ? "--singleflow" : "--nosingleflow",
				config.getEnableImplicitFlows() ? "--implicit" : "--noimplicit",
				config.getEnableStaticFieldTracking() ? "--static" : "--nostatic", 
				"--aplength", Integer.toString(config.getAccessPathLength()),
				"--cgalgo", callgraphAlgorithmToString(config.getCallgraphAlgorithm()),
				config.getEnableCallbacks() ? "--callbacks" : "--nocallbacks",
				config.getEnableExceptionTracking() ? "--exceptions" : "--noexceptions",
				"--layoutmode", layoutMatchingModeToString(config.getLayoutMatchingMode()),
				config.getFlowSensitiveAliasing() ? "--aliasflowsens" : "--aliasflowins",
				config.getComputeResultPaths() ? "--paths" : "--nopaths",
				aggressiveTaintWrapper ? "--aggressivetw" : "--nonaggressivetw",
				"--pathalgo", pathAlgorithmToString(config.getPathBuilder()),
				(summaryPath != null && !summaryPath.isEmpty()) ? "--summarypath" : "",
				(summaryPath != null && !summaryPath.isEmpty()) ? summaryPath : "",
				(resultFilePath != null && !resultFilePath.isEmpty()) ? "--saveresults" : "",
				noTaintWrapper ? "--notaintwrapper" : "",
				config.getEnableTypeChecking() ? "" : "--notypechecking",
//				"--repeatCount", Integer.toString(repeatCount),
				config.getEnableArraySizeTainting() ? "" : "--noarraysize",
				config.getUseThisChainReduction() ? "" : "--safemode",
				config.getLogSourcesAndSinks() ? "--logsourcesandsinks" : "",
				"--callbackanalyzer", callbackAlgorithmToString(config.getCallbackAnalyzer()),
				"--maxthreadnum", Integer.toString(config.getMaxThreadNum()),
				config.getEnableArraySizeTainting() ? "--arraysizetainting" : "",
				config.getEnableArraySizeTainting() ? "--arraysizetainting" : "",
				config.isIccEnabled() ? "--iccmodel " + config.getIccModel() : "",
				config.getOneComponentAtATime() ? "--onecomponentatatime" : "",
				"--aliasalgo", aliasAlgorithmToString(config.getAliasingAlgorithm()),
				"--codeelimination", codeEliminationModeToString(config.getCodeEliminationMode()),
				config.getEnableReflection() ? "--enablereflection" : "",
				config.getEnableCallbackSources() ? "" : "--nocallbacksources",
				};
		System.out.println("Running command: " + executable + " " + Arrays.toString(command));
		try {
			ProcessBuilder pb = new ProcessBuilder(command);
			pb.redirectOutput(new File("out_" + new File(fileName).getName() + "_" + repeatCount + ".txt"));
			pb.redirectError(new File("err_" + new File(fileName).getName() + "_" + repeatCount + ".txt"));
			Process proc = pb.start();
			proc.waitFor();
		} catch (IOException ex) {
			System.err.println("Could not execute timeout command: " + ex.getMessage());
			ex.printStackTrace();
		} catch (InterruptedException ex) {
			System.err.println("Process was interrupted: " + ex.getMessage());
			ex.printStackTrace();
		}
	}
	
	private static String callgraphAlgorithmToString(CallgraphAlgorithm algorihm) {
		switch (algorihm) {
			case AutomaticSelection:
				return "AUTO";
			case CHA:
				return "CHA";
			case VTA:
				return "VTA";
			case RTA:
				return "RTA";
			case SPARK:
				return "SPARK";
			case GEOM:
				return "GEOM";
			default:
				return "unknown";
		}
	}

	private static String layoutMatchingModeToString(LayoutMatchingMode mode) {
		switch (mode) {
			case NoMatch:
				return "NONE";
			case MatchSensitiveOnly:
				return "PWD";
			case MatchAll:
				return "ALL";
			default:
				return "unknown";
		}
	}
	
	private static String pathAlgorithmToString(PathBuilder pathBuilder) {
		switch (pathBuilder) {
			case ContextSensitive:
				return "CONTEXTSENSITIVE";
			case ContextInsensitive :
				return "CONTEXTINSENSITIVE";
			case ContextInsensitiveSourceFinder :
				return "SOURCESONLY";
			default :
				return "UNKNOWN";
		}
	}
	
	private static String callbackAlgorithmToString(CallbackAnalyzer analyzer) {
		switch (analyzer) {
			case Default:
				return "DEFAULT";
			case Fast:
				return "FAST";
			default :
				return "UNKNOWN";
		}
	}

	private static String aliasAlgorithmToString(AliasingAlgorithm algo) {
		switch (algo) {
			case None:
				return "NONE";
			case Lazy:
				return "LAZY";
			case FlowSensitive:
				return "FLOWSENSITIVE";
			case PtsBased:
				return "PTSBASED";
			default :
				return "UNKNOWN";
		}
	}

	private static String codeEliminationModeToString(CodeEliminationMode mode) {
		switch (mode) {
			case NoCodeElimination:
				return "NONE";
			case PropagateConstants:
				return "PROPAGATECONSTS";
			case RemoveSideEffectFreeCode:
				return "REMOVECODE";
			default :
				return "UNKNOWN";
		}
	}

	private static InfoflowResults runAnalysis(final String fileName, final String androidJar) {
		try {
			final long beforeRun = System.nanoTime();

			final SetupApplication app;
			if (null == ipcManager)
			{
				app = new SetupApplication(androidJar, fileName);
			}
			else
			{
				app = new SetupApplication(androidJar, fileName, ipcManager);
			}
			
			// Set configuration object
			app.setConfig(config);
			
			
			if (config.isIccEnabled())
			{
				//Set instrumentation object
				config.setCodeEliminationMode(CodeEliminationMode.NoCodeElimination);
				config.setPathBuilder(PathBuilder.ContextSensitive);
			}
			
			if (noTaintWrapper)
				app.setSootConfig(new IInfoflowConfig() {
					
					@Override
					public void setSootOptions(Options options) {
						options.set_include_all(true);
					}
					
				});
			
			final ITaintPropagationWrapper taintWrapper;
			if (noTaintWrapper)
				taintWrapper = null;
			else if (summaryPath != null && !summaryPath.isEmpty()) {
				System.out.println("Using the StubDroid taint wrapper");
				taintWrapper = createLibrarySummaryTW();
				if (taintWrapper == null) {
					System.err.println("Could not initialize StubDroid");
					return null;
				}
			}
			else {
				final EasyTaintWrapper easyTaintWrapper;
				File twSourceFile = new File("../soot-infoflow/EasyTaintWrapperSource.txt");
				if (twSourceFile.exists())
					easyTaintWrapper = new EasyTaintWrapper(twSourceFile);
				else {
					twSourceFile = new File("EasyTaintWrapperSource.txt");
					if (twSourceFile.exists())
						easyTaintWrapper = new EasyTaintWrapper(twSourceFile);
					else {
						System.err.println("Taint wrapper definition file not found at "
								+ twSourceFile.getAbsolutePath());
						return null;
					}
				}
				easyTaintWrapper.setAggressiveMode(aggressiveTaintWrapper);
				taintWrapper = easyTaintWrapper;
			}
			app.setTaintWrapper(taintWrapper);
			
			System.out.println("Running data flow analysis...");
			app.addResultsAvailableHandler(new MyResultsAvailableHandler());
			final InfoflowResults res = app.runInfoflow("SourcesAndSinks.txt");
			System.out.println("Analysis has run for " + (System.nanoTime() - beforeRun) / 1E9 + " seconds");
			
			if (config.getLogSourcesAndSinks()) {
				if (!app.getCollectedSources().isEmpty()) {
					System.out.println("Collected sources:");
					for (Stmt s : app.getCollectedSources())
						System.out.println("\t" + s);
				}
				if (!app.getCollectedSinks().isEmpty()) {
					System.out.println("Collected sinks:");
					for (Stmt s : app.getCollectedSinks())
						System.out.println("\t" + s);
				}
			}
			
			return res;
		} catch (IOException ex) {
			System.err.println("Could not read file: " + ex.getMessage());
			ex.printStackTrace();
			throw new RuntimeException(ex);
		} catch (XmlPullParserException ex) {
			System.err.println("Could not read Android manifest file: " + ex.getMessage());
			ex.printStackTrace();
			throw new RuntimeException(ex);
		}
	}
	
	/**
	 * Creates the taint wrapper for using library summaries
	 * @return The taint wrapper for using library summaries
	 * @throws IOException Thrown if one of the required files could not be read
	 */
	@SuppressWarnings({ "rawtypes", "unchecked" })
	private static ITaintPropagationWrapper createLibrarySummaryTW()
			throws IOException {
		try {
			Class clzLazySummary = Class.forName("soot.jimple.infoflow.methodSummary.data.provider.LazySummaryProvider");
			Class itfLazySummary = Class.forName("soot.jimple.infoflow.methodSummary.data.provider.IMethodSummaryProvider");
			
			Object lazySummary = clzLazySummary.getConstructor(File.class).newInstance(new File(summaryPath));
			
			ITaintPropagationWrapper summaryWrapper = (ITaintPropagationWrapper) Class.forName
					("soot.jimple.infoflow.methodSummary.taintWrappers.SummaryTaintWrapper").getConstructor
					(itfLazySummary).newInstance(lazySummary);
			
			ITaintPropagationWrapper systemClassWrapper = new ITaintPropagationWrapper() {
				
				private ITaintPropagationWrapper wrapper = new EasyTaintWrapper("EasyTaintWrapperSource.txt");
				
				private boolean isSystemClass(Stmt stmt) {
					if (stmt.containsInvokeExpr())
						return SystemClassHandler.isClassInSystemPackage(
								stmt.getInvokeExpr().getMethod().getDeclaringClass().getName());
					return false;
				}
				
				@Override
				public boolean supportsCallee(Stmt callSite) {
					return isSystemClass(callSite) && wrapper.supportsCallee(callSite);
				}
				
				@Override
				public boolean supportsCallee(SootMethod method) {
					return SystemClassHandler.isClassInSystemPackage(method.getDeclaringClass().getName())
							&& wrapper.supportsCallee(method);
				}
				
				@Override
				public boolean isExclusive(Stmt stmt, Abstraction taintedPath) {
					return isSystemClass(stmt) && wrapper.isExclusive(stmt, taintedPath);
				}
				
				@Override
				public void initialize(InfoflowManager manager) {
					wrapper.initialize(manager);
				}
				
				@Override
				public int getWrapperMisses() {
					return 0;
				}
				
				@Override
				public int getWrapperHits() {
					return 0;
				}
				
				@Override
				public Set<Abstraction> getTaintsForMethod(Stmt stmt, Abstraction d1,
						Abstraction taintedPath) {
					if (!isSystemClass(stmt))
						return null;
					return wrapper.getTaintsForMethod(stmt, d1, taintedPath);
				}
				
				@Override
				public Set<Abstraction> getAliasesForMethod(Stmt stmt, Abstraction d1,
						Abstraction taintedPath) {
					if (!isSystemClass(stmt))
						return null;
					return wrapper.getAliasesForMethod(stmt, d1, taintedPath);
				}
				
			};
			
			Method setFallbackMethod = summaryWrapper.getClass().getMethod("setFallbackTaintWrapper",
					ITaintPropagationWrapper.class);
			setFallbackMethod.invoke(summaryWrapper, systemClassWrapper);
			
			return summaryWrapper;
		}
		catch (ClassNotFoundException | NoSuchMethodException ex) {
			System.err.println("Could not find library summary classes: " + ex.getMessage());
			ex.printStackTrace();
			return null;
		}
		catch (InvocationTargetException ex) {
			System.err.println("Could not initialize library summaries: " + ex.getMessage());
			ex.printStackTrace();
			return null;
		}
		catch (IllegalAccessException | InstantiationException ex) {
			System.err.println("Internal error in library summary initialization: " + ex.getMessage());
			ex.printStackTrace();
			return null;
		}
	}

	private static void printUsage() {
		System.out.println("FlowDroid (c) Secure Software Engineering Group @ EC SPRIDE");
		System.out.println();
		System.out.println("Incorrect arguments: [0] = apk-file, [1] = android-jar-directory");
		System.out.println("Optional further parameters:");
		System.out.println("\t--TIMEOUT n Time out after n seconds (data flow only)");
		System.out.println("\t--PATHTIMEOUT n Time out after n seconds (path reconstruction only)");
		System.out.println("\t--CALLBACKTIMEOUT n Time out after n seconds (callback collection only)");
		System.out.println("\t--SYSTIMEOUT n Hard time out (kill process) after n seconds, Unix only");
		System.out.println("\t--SINGLEFLOW Stop after finding first leak");
		System.out.println("\t--IMPLICIT Enable implicit flows");
		System.out.println("\t--NOSTATIC Disable static field tracking");
		System.out.println("\t--NOEXCEPTIONS Disable exception tracking");
		System.out.println("\t--APLENGTH n Set access path length to n");
		System.out.println("\t--CGALGO x Use callgraph algorithm x");
		System.out.println("\t--NOCALLBACKS Disable callback analysis");
		System.out.println("\t--LAYOUTMODE x Set UI control analysis mode to x");
		System.out.println("\t--ALIASFLOWINS Use a flow insensitive alias search");
		System.out.println("\t--NOPATHS Do not compute result paths");
		System.out.println("\t--AGGRESSIVETW Use taint wrapper in aggressive mode");
		System.out.println("\t--PATHALGO Use path reconstruction algorithm x");
		System.out.println("\t--SUMMARYPATH Path to library summaries");
		System.out.println("\t--SYSFLOWS Also analyze classes in system packages");
		System.out.println("\t--NOTAINTWRAPPER Disables the use of taint wrappers");
		System.out.println("\t--NOTYPECHECKING Do not propagate types along with taints");
		System.out.println("\t--LOGSOURCESANDSINKS Print out concrete source/sink instances");
		System.out.println("\t--CALLBACKANALYZER x Uses callback analysis algorithm x");
		System.out.println("\t--MAXTHREADNUM x Sets the maximum number of threads to be used by the analysis to x");
		System.out.println("\t--ONECOMPONENTATATIME Analyze one component at a time");
		System.out.println("\t--ONESOURCEATATIME Analyze one source at a time");
		System.out.println("\t--ALIASALGO x Use the aliasing algorithm x");
		System.out.println("\t--CODEELIMINATION x Use code elimination mode x");
		System.out.println("\t--ENABLEREFLECTION Enable support for reflective method calls");
		System.out.println("\t--SEQUENTIALPATHPROCESSING Process all taint paths sequentially");
		System.out.println("\t--SINGLEJOINPOINTABSTRACTION Only record one source per join point");
		System.out.println("\t--NOCALLBACKSOURCES Don't treat parameters of callback methods as sources");
		System.out.println();
		System.out.println("Supported callgraph algorithms: AUTO, CHA, RTA, VTA, SPARK, GEOM");
		System.out.println("Supported layout mode algorithms: NONE, PWD, ALL");
		System.out.println("Supported path algorithms: CONTEXTSENSITIVE, CONTEXTINSENSITIVE, SOURCESONLY");
		System.out.println("Supported callback algorithms: DEFAULT, FAST");
		System.out.println("Supported alias algorithms: NONE, PTSBASED, FLOWSENSITIVE, LAZY");
		System.out.println("Supported code elimination modes: NONE, PROPAGATECONSTS, REMOVECODE");
	}

}