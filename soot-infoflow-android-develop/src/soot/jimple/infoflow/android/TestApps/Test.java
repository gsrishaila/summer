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
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.StringReader;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Spliterator;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import javax.xml.stream.XMLStreamException;

import org.xmlpull.v1.XmlPullParserException;

import com.sun.corba.se.impl.orbutil.graph.GraphImpl;

import soot.Body;
import soot.MethodOrMethodContext;
import soot.PackManager;
import soot.PatchingChain;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.UnitBox;
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
import soot.tagkit.Tag;
import soot.toolkits.graph.Block;
import soot.toolkits.graph.BlockGraph;
import soot.toolkits.graph.BlockGraphConverter;
import soot.toolkits.graph.BriefBlockGraph;
import soot.toolkits.graph.CompleteBlockGraph;
import soot.toolkits.graph.DirectedGraph;
import soot.toolkits.graph.ExceptionalGraph;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.HashMutableDirectedGraph;
import soot.toolkits.graph.MHGDominatorsFinder;
import soot.toolkits.graph.MutableDirectedGraph;
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
	
	private static boolean aggressiveTaintWrapper = false;
	private static boolean noTaintWrapper = false;
	private static String summaryPath = "";
	private static String resultFilePath = "";
	
	//create a list of the soot methods name
	static List<String> sootMethodsNameList = new ArrayList<String>();
	static List<String> sootMethodsSignatureList = new ArrayList<String>();
	static List<String> sootMethodsSubSignatureList = new ArrayList<String>();
	static List<SootMethod> sootMethodsObjectList = new ArrayList<SootMethod>();

	
	private static IIPCManager ipcManager = null;
	public static void setIPCManager(IIPCManager ipcManager)
	{
		Test.ipcManager = ipcManager;
	}
	public static IIPCManager getIPCManager()
	{
		return Test.ipcManager;
	}
	
	//added in function to get the call graph as dot file
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
		System.out.println("Method Name : " + entryPoint.getName());
		System.out.println("Method Signature : " + entryPoint.getSignature());
		
		Body b = entryPoint.retrieveActiveBody();
		
		BlockGraph bg = new BriefBlockGraph(b);
		
		MHGDominatorsFinder<Block> domFinder = new MHGDominatorsFinder(bg); 
		//print basic block info 
		for (Block block:bg){
			System.out.println("\n"+block.toString());
		}//end for 
		
		DirectedGraph<Unit> x = new ExceptionalUnitGraph(entryPoint.getActiveBody());
        CFGToDotGraph y = new CFGToDotGraph();
        //DotGraph a=y.drawCFG(x,entryPoint.getActiveBody()); //gives units in cfg
        DotGraph a=y.drawCFG(bg,entryPoint.getActiveBody());
        a.plot(entryPoint.getSignature()+".dot");
		System.out.println("***End of CFG Generation***" + entryPoint.getName()+"\n");
	}
	
	//Function added in to generate the CFG111
		public static void generateCFG111 (SootMethod entryPoint)
		{
			System.out.println("***CFG Generation111***" + entryPoint.getName());
			System.out.println("Method Name : " + entryPoint.getName());
			System.out.println("Method Signature : " + entryPoint.getSignature());
			
			Body b = entryPoint.retrieveActiveBody();
			
			BlockGraph bg = new BriefBlockGraph(b);
			
			MHGDominatorsFinder<Block> domFinder = new MHGDominatorsFinder(bg); 
			//print basic block info 
			for (Block block:bg){
				System.out.println("\n"+block.toString());
				/*if (block.getIndexInMethod()==6)
				{
					List<Block> originalSuccessorList=new ArrayList();
					originalSuccessorList.addAll(block.getSuccs());
					originalSuccessorList.add(bg.getBlocks().get(9));
					block.setSuccs(originalSuccessorList);
				}*/
			}//end for 
			
			DirectedGraph<Unit> x = new ExceptionalUnitGraph(entryPoint.getActiveBody());
			//***code to add the cfgs together***
			//SootMethod m = c.getMethodByName(methodName);
			/*if(entryPoint.getName() == "dummyMainMethod")
			{
				Body body = entryPoint.retrieveActiveBody();
			    //Build CFG
			    UnitGraph cfg = new ExceptionalUnitGraph(body);
			    PatchingChain<Unit> allunits = body.getUnits();
			    for (Unit eachunit:allunits) 
			    {
			    	
			    	System.out.println("each unit to string: "+eachunit+"\n");
				}
			}*/
			//***code to add the cfgs together***
	        CFGToDotGraph y = new CFGToDotGraph();
	        //DotGraph a=y.drawCFG(x,entryPoint.getActiveBody());//gives units in cfg
	        DotGraph a=y.drawCFG(bg,entryPoint.getActiveBody());
	        
	        a.plot(entryPoint.getName()+"111.dot");
			
			System.out.println("***End of CFG Generation***" + entryPoint.getName()+"\n");
		}
	
	
	public static void mergeCFG2s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{
		Unit successor = null;
		Unit predecessor = null;
		for (SootMethod mdt:entryPoint)
    	{
    		if(mdt.getName().contains("dummyMainMethod"))
			{
    			Body body = mdt.retrieveActiveBody();
			    //Build CFG
			    UnitGraph cfg = new ExceptionalUnitGraph(body);
			    PatchingChain<Unit> allunits = body.getUnits();
			    for (Unit eachunit:allunits) 
			    {
			    	//System.out.println("unitToString : "+eachunit.toString()+"\n");
			    	if (eachunit.toString().contains("invoke") && (!eachunit.toString().contains("if")))
			    	{
			    		
			    		for (String mdtSig:sootMethodsSignatureList) 
			    		{
			    			if (eachunit.toString().contains(mdtSig))
			    			{
			    				//get successor of this unit
			    				System.out.println("*****");
			    				System.out.println("dummy UnitToString  : " + eachunit.toString());
			    				System.out.println("mdt Name  : " + mdtSig.toString());
			    				successor = mdt.retrieveActiveBody().getUnits().getSuccOf(eachunit);
			    				predecessor = mdt.retrieveActiveBody().getUnits().getPredOf(eachunit);
			    				System.out.println("successor  : " + successor.toString());
			    				System.out.println("predecessor  : " + predecessor.toString());
			    				System.out.println("*****");
			    				
			    				//eachunit.redirectJumpsToThisTo(successor);
			    				List<UnitBox> before =successor.getBoxesPointingToThis();
			    				for (UnitBox b4UnitBox:before)
			    				{
			    					System.out.println("successor units b4  : " + b4UnitBox.getUnit().toString());	
			    				}
			    				mdt.getActiveBody().getUnits().getSuccOf(predecessor).redirectJumpsToThisTo(successor);//not working
			    				List<UnitBox> after =successor.getBoxesPointingToThis();
			    				for (UnitBox afterUnitBox:before)
			    				{
			    					System.out.println("successor units b4  : " + afterUnitBox.getUnit().toString());	
			    				}
			    				generateCFG111 (mdt);
			    				/*//look for the unit box with the successor and the predecessor
			    				List<UnitBox> listOfUnitBoxes = mdt.getActiveBody().getAllUnitBoxes();
			    				for (UnitBox currUnitBox:listOfUnitBoxes)
			    				{
			    					//if(currUnitBox.getUnit().toString().equals(successor.toString()))
			    					if(currUnitBox.getUnit().equals(successor))
			    						System.out.println("successor box found  : " + currUnitBox.getUnit().toString());
			    					if(currUnitBox.getUnit().equals(predecessor))
			    						System.out.println("predecessor box found  : " + currUnitBox.getUnit().toString());
			    				}*/
			    				return;
			    			}
			    		}
			    	}
			    }
			}
    	
    	}
	}
	
	public static void mergeCFG11s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{
		Body body = null ;
		//first get the dummy main mdt and its body
		for (SootMethod eachMdt:entryPoint)
		{
			if (eachMdt.getName().contains("dummyMainMethod") )
			{
				body = eachMdt.retrieveActiveBody();
			}
		}
		
		for (SootMethod eachMdt:entryPoint)
		{
			//get the units frm dummy method
			PatchingChain<Unit> unitsInDummyMdt = body.getUnits();
			//get the dummymainmdt
			if (eachMdt.getSignature() == "dummyMainMethod" )
				continue;
			if(unitsInDummyMdt == null)
			{
				System.out.println("unitsInDummyMdt is null");
			}
			else
			{
				for (Unit unitFrmMdt:unitsInDummyMdt)
				{
					if (unitFrmMdt.toString().contains("invoke") && (!unitFrmMdt.toString().contains("if")))
					{
						 Unit successor = body.getUnits().getSuccOf(unitFrmMdt);
						 Unit successorSuccessor = body.getUnits().getSuccOf(successor);
						 if (unitFrmMdt.toString().contains(eachMdt.getSignature()))
						 {
							
							 
							 //eachMdt.retrieveActiveBody().getUnits().removeLast();
							 //get the tail of the methods
							 UnitGraph unitGrpOfNewFunc= new ExceptionalUnitGraph (eachMdt.getActiveBody());
							
							// newone.getTails();
							 for (Unit tails:unitGrpOfNewFunc.getTails())
							 {
								 //tailclone
								 Unit tailClone = (Unit) tails.clone();
								 //clone the successor
								 Unit clone= (Unit) successor.clone();
								 System.out.println("Tail : "+tails.toString());
								 System.out.println("unitFrmMdt : "+unitFrmMdt.toString());
								 System.out.println("Successor : "+successor.toString());
								 unitGrpOfNewFunc.getBody().getUnits().swapWith(tails, clone);
								 //cannot insert the return anymore
								 //unitGrpOfNewFunc.getBody().getUnits().insertBefore(tailClone, clone);
				
								 //BlockGraph bg = new BriefBlockGraph(unitGrpOfNewFunc.getBody());
								 //CFGToDotGraph y = new CFGToDotGraph();
							     //DotGraph a1=y.drawCFG(bg,body);
							     //a1.plot(eachMdt.getName()+"444.dot");
								 break;
							 }
							 //remove the successor from the dummy
							 body.getUnits().remove(successor);
							 
							 
							 //merge it with successorSuccessor
							 System.out.println("eachMdt unit size: "+eachMdt.retrieveActiveBody().getUnits().size());
							 body.getUnits().insertOnEdge(eachMdt.retrieveActiveBody().getUnits(),unitFrmMdt, successorSuccessor);
							 BlockGraph bg = new BriefBlockGraph(body);
							 CFGToDotGraph y = new CFGToDotGraph();
						     DotGraph a1=y.drawCFG(bg,body);
						     a1.plot("dummyMainMethod333.dot");
						     break;
						     //original part
						 }
					}
				}
			}
		}
	}
	
	public static void addingDummyTail (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{
		Stmt nop=Jimple.v().newNopStmt();
		Stmt nop1=Jimple.v().newNopStmt();
		Unit tailUnit1 = null;
		//get all 
		
		for (SootMethod eachMdt:entryPoint)
		{
			if (eachMdt.getName().contains("dummyMainMethod") )
				continue;
			UnitGraph unitGrpOfNewFunc= new ExceptionalUnitGraph (eachMdt.getActiveBody());
			//create MutableDirectedGraph ***** 
			//create a map of units vs list of their successors
			Map<Unit, List<Unit>> unitsSuccMap = new HashMap<Unit, List<Unit>>();
			for (Unit inBodyUnit:eachMdt.getActiveBody().getUnits())
			{
				List<Unit> succUnitList = new ArrayList();
				succUnitList=unitGrpOfNewFunc.getSuccsOf(inBodyUnit);
				unitsSuccMap.put(inBodyUnit, succUnitList);
			}
			
	        HashMutableDirectedGraph  mutablegraph = new HashMutableDirectedGraph  ();
			
			
			//find out if the cfg has 2 tails
			List<Unit> tailList1 = new ArrayList();
			for (Unit tail:unitGrpOfNewFunc.getTails())
			{
				tailList1.add(tail);
				tailUnit1 = (Unit) tail.clone();
			}
			if(unitGrpOfNewFunc.getTails().size()>1)
			{
				System.out.println("This function went through if statement : "+eachMdt.getSignature());
				//first construct this graph inside the mutablegraph
				for (Map.Entry<Unit, List<Unit>> entry : unitsSuccMap.entrySet() )
				{
					for (Unit succUnit:entry.getValue())
					{
						if(!mutablegraph.containsNode(entry.getKey()))
							mutablegraph.addNode(entry.getKey());
						if(!mutablegraph.containsNode(succUnit))
							mutablegraph.addNode(succUnit);
						mutablegraph.addEdge(entry.getKey(), succUnit);
						
					}
				}
				Body bi = eachMdt.retrieveActiveBody();
		        CompleteBlockGraph cfg = new CompleteBlockGraph(bi);
		        System.out.println(cfg);
		        //*****
		        BlockGraph newbg= new  BriefBlockGraph (eachMdt.retrieveActiveBody());
		        /*Parameters:
					aHead - The first unit ir this Block.
					aTail - The last unit in this Block.
					aBody - The Block's enclosing Body instance.
					aIndexInMethod - The index of this Block in the list of Blocks that partition it's enclosing Body instance.
					BlockLength - The number of units that makeup this block.
					aBlockGraph - The Graph of Blocks in which this block lives.*/
		        Block newtailblk = new Block (eachMdt.getActiveBody().getUnits().getFirst(),eachMdt.getActiveBody().getUnits().getFirst(),newbg.getBody(),newbg.getBlocks().size(),2,newbg);
		        //DummyBlock tail = new DummyBlock(cfg.getBody(),cfg.getBlocks().size());
		        

		        List<Block> succUnitList = new ArrayList();
		        List<Block> predUnitList = new ArrayList();
		        succUnitList.add(newtailblk);
		        for (Block incfg:cfg)
		        {
		        	for (Unit tailUnit:tailList1)
		        	{
		        		if (incfg.toString().contains(tailUnit.toString()))
		        		{
		        			System.out.println("TailUnit : "+tailUnit.toString());
		        			System.out.println("Block : "+ incfg.toString());
		        			incfg.remove(tailUnit);
		        		    predUnitList.add(incfg);
		        			incfg.setSuccs(succUnitList);
		        			newtailblk.setPreds(predUnitList);
		        			break;
		        		}
		        	}
		        }
		        cfg.getBody().getUnits().swapWith(cfg.getBody().getUnits().getLast(), tailUnit1);
		        //System.out.println(cfg);
		        //*******
		        //BlockGraphConverter.addStartStopNodesTo(cfg);
		        
		        System.out.println("cfg.getBody().getlast : "+cfg.getBody().getUnits().getLast().toString());
		        System.out.println("tailUnit1 : "+tailUnit1.toString());
		        System.out.println("NewTail : "+newtailblk.toString());
		        //System.out.println(cfg);
		        
		        BlockGraph bg1 = new BriefBlockGraph(cfg.getBody());
				CFGToDotGraph y1 = new CFGToDotGraph();
			    DotGraph a11=y1.drawCFG(bg1,cfg.getBody());
			    a11.plot(eachMdt.getSignature()+"555.dot");
			}
			
			//mutablegraph.printGraph();
			//Body b=((ExceptionalGraph<Unit>) mutablegraph).getBody();
			//BlockGraph bg1 = new BriefBlockGraph(b);
			//CFGToDotGraph y1 = new CFGToDotGraph();
		    //DotGraph a11=y1.drawCFG(bg1,b);
		    //a11.plot(eachMdt.getSignature()+"555.dot");
		    
		    
			
			//create MutableDirectedGraph *****
			//mutablegraph.addEdge(from, to);
			
			
			List<Unit> tailList = new ArrayList();
			tailList=unitGrpOfNewFunc.getTails();
			//get the dummymainmdt
			if (eachMdt.getSignature() == "dummyMainMethod" )
				continue;
			for (Unit tail:tailList)
			{
				Unit nopUnit = (Unit) nop.clone();
				//eachMdt.getActiveBody().getUnits().remove(tail);
				eachMdt.getActiveBody().getUnits().swapWith(tail, nopUnit);
			}
				
			
			BlockGraph bg = new BriefBlockGraph(eachMdt.getActiveBody());
			CFGToDotGraph y = new CFGToDotGraph();
		    DotGraph a1=y.drawCFG(bg,eachMdt.getActiveBody());
		    a1.plot(eachMdt.getSignature()+"444.dot");
		    //break;	
		}
	}
	
	public static void mergeCFG10s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{	
		List<Unit> tailList = new ArrayList();
		Body body = null ;
		SootMethod dummyMainMdt = null ;
		//first get the dummy main mdt and its body
		for (SootMethod eachMdt:entryPoint)
		{
			if (eachMdt.getName().contains("dummyMainMethod") )
			{
				body = eachMdt.retrieveActiveBody();
				dummyMainMdt = eachMdt;
			}
		}
		
		for (SootMethod eachMdt:entryPoint)
		{
			//get the units frm dummy method
			PatchingChain<Unit> unitsInDummyMdt = body.getUnits();
			//get the dummymainmdt
			if (eachMdt.getSignature() == "dummyMainMethod" )
				continue;
			if(unitsInDummyMdt == null)
			{
				System.out.println("unitsInDummyMdt is null");
			}
			else
			{
				for (Unit unitFrmMdt:unitsInDummyMdt)
				{
					//if (unitFrmMdt.toString().contains("invoke") && (!unitFrmMdt.toString().contains("if")) && (eachMdt.getSignature().contains("onOptionsItemSelected")))
					if (unitFrmMdt.toString().contains("invoke") && (!unitFrmMdt.toString().contains("if")))
					{
						
						 if (unitFrmMdt.toString().contains(eachMdt.getSignature()))
						 {
							 Unit successor = body.getUnits().getSuccOf(unitFrmMdt);
							 List<Unit> nonRetUnits = new ArrayList();
							 /*if(!unitFrmMdt.toString().contains("return"))
								 nonRetUnits.add(unitFrmMdt);*/ 
							 //remove all units with return in it
							 //eachMdt.retrieveActiveBody().getUnits().retainAll(nonRetUnits);
							 
							 //removing tails instead
							 
							 //removing tails instead
							 
							 eachMdt.retrieveActiveBody().getUnits().removeLast();
							 //*****get the other tails*****
							 Unit b4Tail = null;
							 UnitGraph newone= new ExceptionalUnitGraph (eachMdt.getActiveBody());
							 
							 //only if there are other tails
							 int remainingTails=0;
							 remainingTails = newone.getTails().size();
							 if(remainingTails>0)
							 {
								 for (Unit eachTailUnit:newone.getTails())
								 {
									 tailList.add(eachTailUnit);
									 System.out.println("eachTailUnit : "+eachTailUnit.toString());
									 b4Tail =newone.getBody().getUnits().getPredOf(eachTailUnit);
									 System.out.println("eachTailUnit : "+b4Tail.toString());
									 body.getUnits().remove(eachTailUnit); //added in *****get the other tails***** 
									 //connect the b4Tail to the successor
								 }
							 }
							//*****get the other tails*****
							 System.out.println("eachMdt unit size: "+eachMdt.retrieveActiveBody().getUnits().size());
							 body.getUnits().insertOnEdge(eachMdt.retrieveActiveBody().getUnits(),unitFrmMdt, successor);
							 if(remainingTails>0)
								 body.getUnits().insertAfter(successor, b4Tail); //added in *****get the other tails***** 
							
							 //added in part
							 /*if(eachMdt.getName().contains("onOptionsItemSelected") )
							 {
								 UnitGraph newone= new ExceptionalUnitGraph (eachMdt.getActiveBody());
								 newone.getBody()body.getUnits().
								// newone.getTails();
								 for (Unit tails:newone.getTails())
								 {
									 System.out.println("Tail : "+tails.toString());
								 }
							 }*/
							 
							 /*if(eachMdt.getName().contains("onOptionsItemSelected") )
							 {
								 Iterator it = eachMdt.getActiveBody().getUnits().snapshotIterator();
								 while (it.hasNext())
								 {
									 Stmt u = (Stmt) it.next();
									 System.out.println("Stmt : "+u.toString());
									 u.
								 }
								
							 }*/
								 
		
							 
							 /*if(eachMdt.getName().contains("onOptionsItemSelected") )
							 {
							 UnitGraph unitGrp = new ExceptionalUnitGraph(eachMdt.getActiveBody());
							 Map<Unit, List<Unit>> unitToSuccs = new HashMap<>();
							 Map<Unit, List<Unit>> unitToPreds = new HashMap<>();
							 
							 List<Unit> succList = new ArrayList();
							 List<Unit> predList = new ArrayList();
							 
							 for (Unit eachunit:eachMdt.getActiveBody().getUnits())
							 {
								 succList.add(body.getUnits().getSuccOf(eachunit));
								 unitToSuccs.put(eachunit, succList);
								 
								 predList.add(body.getUnits().getPredOf(eachunit));
								 unitToSuccs.put(eachunit, predList);
								 
								 succList.clear();
								 predList.clear();
							 }
							 unitGrp.addEdge(unitToSuccs,unitToPreds,unitGrp.getBody().getUnits().getFirst(),unitGrp.getBody().getUnits().getLast());
							 
							 BlockGraph bg = new BriefBlockGraph(unitGrp.getBody());
							 CFGToDotGraph y = new CFGToDotGraph();
						     DotGraph a1=y.drawCFG(bg,body);
						     a1.plot(eachMdt.getName()+"444.dot");
						     
							 }
							 break;*/
							 //added in part
							 
							 //original part
							 BlockGraph bg = new BriefBlockGraph(body);
							 //remove blocks with any of the tails we found earlier
							 //To do:
							 List<Block> blkToRemove = new ArrayList();
							 Unit toDeleteHead  = null;
							 Unit toDeleteTail = null;
							 for (Block blksInBg:bg.getBlocks())
							 {
								 System.out.println("Block idx : "+ blksInBg.getIndexInMethod());
								 System.out.println("Block Tail : "+ blksInBg.getTail().toString());
								 for(Unit isTailInBlk:tailList)
								 {	 if(blksInBg.getTail().equals(isTailInBlk))
									 {
										 System.out.println("Tail found in this blk");
										 blkToRemove.add(blksInBg);
										 //assuming the blkToRemove Only Contains two units
										 //ie successor duplicate  and the tail ...these two are found in this block
										 toDeleteHead = blksInBg.getHead();
										 toDeleteTail = blksInBg.getTail();
										 
									 }
								 }
								 //blksInBg.getTail();
							 }
							 List<Block> updatedList = new ArrayList();
							 for (Block b:bg.getBlocks())
								 updatedList.add(b);
							 //BlockGraph bg1 = new BriefBlockGraph(null);
							 for (Block toRemove:blkToRemove)
							 {
								 updatedList.remove(toRemove);
								 //bg.setBlocks(updatedList);
							 }
							 
							 //remove the tailunit frm the unitgraph
							 //UnitGraph newone1 = new ExceptionalUnitGraph (eachMdt.getActiveBody());
							 UnitGraph newone1= new ExceptionalUnitGraph (body);
							 newone1.getBody();
							 //delete the additional duplicate units
							 if(toDeleteHead  != null && toDeleteTail != null)
							 {
								 //body.getUnits().remove(toDeleteTail);
								 //body.getUnits().remove(toDeleteHead);
							 }
							 
							 CompleteBlockGraph cfg = new CompleteBlockGraph(body);
							 BlockGraphConverter.addStartStopNodesTo(cfg);
						     //System.out.println(cfg);
						     bg = new BriefBlockGraph (cfg.getBody());
							 //remove the tailunit from the unitgraph
							 
							 //remove blocks with any of the tails we found earlier
							 CFGToDotGraph y = new CFGToDotGraph();
						     DotGraph a1=y.drawCFG(bg,body);
						     a1.plot("dummyMainMethod333.dot");
						     generateCFG (dummyMainMdt);
						     break;
						     //original part
						 }
					}
				}
			}
		}
	}
	
	
	public static void mergeCFG101s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{	
		List<Unit> tailList = new ArrayList();
		Body body = null ;
		SootMethod dummyMainMdt = null ;
		//first get the dummy main mdt and its body
		for (SootMethod eachMdt:entryPoint)
		{
			if (eachMdt.getName().contains("dummyMainMethod") )
			{
				body = eachMdt.retrieveActiveBody();
				dummyMainMdt = eachMdt;
			}
		}
		
		for (SootMethod eachMdt:entryPoint)
		{
			//get the units frm dummy method
			PatchingChain<Unit> unitsInDummyMdt = body.getUnits();
			//get the dummymainmdt
			if (eachMdt.getSignature() == "dummyMainMethod" )
				continue;
			if(unitsInDummyMdt == null)
			{
				System.out.println("unitsInDummyMdt is null");
			}
			else
			{
				for (Unit unitFrmMdt:unitsInDummyMdt)
				{
					//if (unitFrmMdt.toString().contains("invoke") && (!unitFrmMdt.toString().contains("if")) && (eachMdt.getSignature().contains("onOptionsItemSelected")))
					if (unitFrmMdt.toString().contains("invoke") && (!unitFrmMdt.toString().contains("if")))
					{
						
						 if (unitFrmMdt.toString().contains(eachMdt.getSignature()))
						 {
							 Unit successor = body.getUnits().getSuccOf(unitFrmMdt);
							 List<Unit> nonRetUnits = new ArrayList();
							 /*if(!unitFrmMdt.toString().contains("return"))
								 nonRetUnits.add(unitFrmMdt);*/ 
							 //remove all units with return in it
							 //eachMdt.retrieveActiveBody().getUnits().retainAll(nonRetUnits);
							 
							 //removing tails instead
							 
							 //removing tails instead
							 
							 eachMdt.retrieveActiveBody().getUnits().removeLast();
							 //*****get the other tails*****
							 Unit b4Tail = null;
							 UnitGraph newone= new ExceptionalUnitGraph (eachMdt.getActiveBody());
							 
							 //only if there are other tails
							 int remainingTails=0;
							 Stmt nop=Jimple.v().newNopStmt();
							 Unit cloneNexUnit = (Unit) nop.clone();
							 remainingTails = newone.getTails().size();
							 if(remainingTails>0)
							 {
								 for (Unit eachTailUnit:newone.getTails())
								 {
									 tailList.add(eachTailUnit);
									 System.out.println("eachTailUnit : "+eachTailUnit.toString());
									 b4Tail =newone.getBody().getUnits().getPredOf(eachTailUnit);
									 System.out.println("eachTailUnit : "+b4Tail.toString());
									 newone.getBody().getUnits().swapWith(eachTailUnit, cloneNexUnit);
									 //body.getUnits().remove(eachTailUnit); //added in *****get the other tails***** 
									 //connect the b4Tail to the successor
								 }
							 }
							//*****get the other tails*****
							 System.out.println("eachMdt unit size: "+eachMdt.retrieveActiveBody().getUnits().size());
							 body.getUnits().insertOnEdge(eachMdt.retrieveActiveBody().getUnits(),unitFrmMdt, successor);
							 if(remainingTails>0)
								 body.getUnits().insertAfter(successor, cloneNexUnit); //added in *****get the other tails***** 
							
							 //added in part
							 /*if(eachMdt.getName().contains("onOptionsItemSelected") )
							 {
								 UnitGraph newone= new ExceptionalUnitGraph (eachMdt.getActiveBody());
								 newone.getBody()body.getUnits().
								// newone.getTails();
								 for (Unit tails:newone.getTails())
								 {
									 System.out.println("Tail : "+tails.toString());
								 }
							 }*/
							 
							 /*if(eachMdt.getName().contains("onOptionsItemSelected") )
							 {
								 Iterator it = eachMdt.getActiveBody().getUnits().snapshotIterator();
								 while (it.hasNext())
								 {
									 Stmt u = (Stmt) it.next();
									 System.out.println("Stmt : "+u.toString());
									 u.
								 }
								
							 }*/
								 
		
							 
							 /*if(eachMdt.getName().contains("onOptionsItemSelected") )
							 {
							 UnitGraph unitGrp = new ExceptionalUnitGraph(eachMdt.getActiveBody());
							 Map<Unit, List<Unit>> unitToSuccs = new HashMap<>();
							 Map<Unit, List<Unit>> unitToPreds = new HashMap<>();
							 
							 List<Unit> succList = new ArrayList();
							 List<Unit> predList = new ArrayList();
							 
							 for (Unit eachunit:eachMdt.getActiveBody().getUnits())
							 {
								 succList.add(body.getUnits().getSuccOf(eachunit));
								 unitToSuccs.put(eachunit, succList);
								 
								 predList.add(body.getUnits().getPredOf(eachunit));
								 unitToSuccs.put(eachunit, predList);
								 
								 succList.clear();
								 predList.clear();
							 }
							 unitGrp.addEdge(unitToSuccs,unitToPreds,unitGrp.getBody().getUnits().getFirst(),unitGrp.getBody().getUnits().getLast());
							 
							 BlockGraph bg = new BriefBlockGraph(unitGrp.getBody());
							 CFGToDotGraph y = new CFGToDotGraph();
						     DotGraph a1=y.drawCFG(bg,body);
						     a1.plot(eachMdt.getName()+"444.dot");
						     
							 }
							 break;*/
							 //added in part
							 
							 //original part
							 BlockGraph bg = new BriefBlockGraph(body);
							 //remove blocks with any of the tails we found earlier
							 //To do:
							 List<Block> blkToRemove = new ArrayList();
							 Unit toDeleteHead  = null;
							 Unit toDeleteTail = null;
							 for (Block blksInBg:bg.getBlocks())
							 {
								 System.out.println("Block idx : "+ blksInBg.getIndexInMethod());
								 System.out.println("Block Tail : "+ blksInBg.getTail().toString());
								 for(Unit isTailInBlk:tailList)
								 {	 if(blksInBg.getTail().equals(isTailInBlk))
									 {
										 System.out.println("Tail found in this blk");
										 blkToRemove.add(blksInBg);
										 //assuming the blkToRemove Only Contains two units
										 //ie successor duplicate  and the tail ...these two are found in this block
										 toDeleteHead = blksInBg.getHead();
										 toDeleteTail = blksInBg.getTail();
										 
									 }
								 }
								 //blksInBg.getTail();
							 }
							 List<Block> updatedList = new ArrayList();
							 for (Block b:bg.getBlocks())
								 updatedList.add(b);
							 //BlockGraph bg1 = new BriefBlockGraph(null);
							 for (Block toRemove:blkToRemove)
							 {
								 updatedList.remove(toRemove);
								 //bg.setBlocks(updatedList);
							 }
							 
							 //remove the tailunit frm the unitgraph
							 //UnitGraph newone1 = new ExceptionalUnitGraph (eachMdt.getActiveBody());
							 UnitGraph newone1= new ExceptionalUnitGraph (body);
							 newone1.getBody();
							 //delete the additional duplicate units
							 if(toDeleteHead  != null && toDeleteTail != null)
							 {
								 //body.getUnits().remove(toDeleteTail);
								 //body.getUnits().remove(toDeleteHead);
							 }
							 
							 CompleteBlockGraph cfg = new CompleteBlockGraph(body);
							 BlockGraphConverter.addStartStopNodesTo(cfg);
						     //System.out.println(cfg);
						     bg = new BriefBlockGraph (cfg.getBody());
							 //remove the tailunit from the unitgraph
							 
							 //remove blocks with any of the tails we found earlier
							 CFGToDotGraph y = new CFGToDotGraph();
						     DotGraph a1=y.drawCFG(bg,body);
						     a1.plot("dummyMainMethod333.dot");
						     generateCFG (dummyMainMdt);
						     break;
						     //original part
						 }
					}
				}
			}
		}
	}
	public static PatchingChain<Unit> getDummyUnits (List <SootMethod> entryPoint)
	{
		PatchingChain<Unit> allunits = null;
		for (SootMethod eachMdt:entryPoint)
		{
			System.out.println("Each Signature : "+ eachMdt.getSignature());//only once
			//for each of the mdt look for the unit that calls this mdt
			if(eachMdt.getName().contains("dummyMainMethod"))
			{
    			Body body = eachMdt.retrieveActiveBody();
			    //Build CFG
			    //UnitGraph cfg = new ExceptionalUnitGraph(body);
			    allunits = body.getUnits();
			}
		}
		return allunits;
	}
	public static void mergeCFG9s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{
		List<String> mergedFunctions = new ArrayList();
		for (SootMethod mdt:entryPoint)
		{
			if(mdt.getName().contains("dummyMainMethod"))
			{
				Body body = mdt.retrieveActiveBody();
				
				BlockGraph bg = new BriefBlockGraph(body);
				int currNoBlks = bg.getBlocks().size();
				System.out.println("Curr No of Blks: "+currNoBlks);//only once
				/*for (UnitBox unitInBlk:mdt.getActiveBody().getAllUnitBoxes())
				{
					System.out.println("unitInBlock : "+unitInBlk.getUnit().toString());//only once
				}*/
				for (Unit unitInBlk:mdt.getActiveBody().getUnits())
				{
					System.out.println("Content : "+unitInBlk.toString());
					if (unitInBlk.toString().contains("invoke") && (!unitInBlk.toString().contains("if")))
					{
						for (SootMethod mdt1:entryPoint) 
				    	 {
							 if (unitInBlk.toString().contains(mdt1.getSignature()))
							 {
								 if (mergedFunctions.contains(mdt1.getSignature()))
									 break;
								 mergedFunctions.add(mdt1.getSignature());
								 //we found the sootmdt that is being called
								 //get the  successor to this unit //assuming its just one
								 Unit successor = body.getUnits().getSuccOf(unitInBlk);
								 //added in
								 Unit predecessor = body.getUnits().getPredOf(unitInBlk);//predecessor of this unit
								 Unit successorSuccessor = body.getUnits().getSuccOf(successor);
								 //added in
								 //add successor unit after the last unit of mdt1
								 //mdt1.getActiveBody().getUnits().insertAfter(body.getUnits().getSuccOf(unitInBlk),mdt1.getActiveBody().getUnits().getLast());
								 //redirect the jump
								 //mdt1.getActiveBody().getUnits().getLast().redirectJumpsToThisTo(successor);
								//redirect the jump
								 //remove the successor
								 //mdt.getActiveBody().getUnits().remove(successor);
								 //mdt.getActiveBody().getUnits().insertAfter(mdt1.getActiveBody().getUnits(),unitInBlk);
								 
							
								 
								//added in
								 //mdt.getActiveBody().getUnits().remove(successor);
								 //mdt.getActiveBody().getUnits().insertAfter(successor,unitInBlk);
								 //mdt.getActiveBody().getUnits().insertAfter(successorSuccessor,successor);
								 //mdt.getActiveBody().getUnits().insertOnEdge(successor, unitInBlk,successorSuccessor);//not working
								 //mdt.getActiveBody().getUnits().insertOnEdge(mdt1.getActiveBody().getUnits().getFirst(), unitInBlk, successor);
								// Tag tagInfo ="kkk";
								 //Tag example = tagInfo;
								// mdt1.getActiveBody().getUnits().getLast().
								 mdt1.getActiveBody().getUnits().removeLast();
								 mdt.getActiveBody().getUnits().insertOnEdge(mdt1.getActiveBody().getUnits(), unitInBlk, successor);
								//added in
								 
								 bg = new BriefBlockGraph(mdt.retrieveActiveBody());
								 CFGToDotGraph y = new CFGToDotGraph();
							     DotGraph a1=y.drawCFG(bg,mdt.getActiveBody());
							     a1.plot(mdt.getName()+"333.dot");
							 }
				    	 }
					}
					//break because java.util.ConcurrentModificationException
					//break;
				}
				
			}
		}
	}
	public static void mergeCFG8s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{
		for (SootMethod mdt:entryPoint)
		{
			System.out.println("again... ");//only once
			if(mdt.getName().contains("dummyMainMethod"))
			{
				Body body = mdt.retrieveActiveBody();
				BlockGraph bg = new BriefBlockGraph(body);
				int currNoBlks = bg.getBlocks().size();
				System.out.println("Curr No of Blks: "+currNoBlks);//only once
				for (Block block:bg.getBlocks())
				{
					System.out.println("\nblock content: "+block.toString());
					if (block.toString().contains("invoke"))
					{
						String blkContent = block.toString();
						BufferedReader bufReader = new BufferedReader(new StringReader(blkContent));
						String line=null;
						try {
							while( (line=bufReader.readLine()) != null )
							{
								System.out.println("\nblock content, line by line...: "+line);
								if (line.contains("invoke") && (!line.contains("if")))
								{
									//thrs a function call in this block, find which one
									for (SootMethod mdt1:entryPoint) 
							    	 {
										 if (line.contains(mdt1.getSignature()))
										 {
											 System.out.println("\nfunc call in line "+mdt1.getSignature());
											 //System.out.println("\nblock successor list b4 : "+ block.getSuccs());
											 //attach the cfg of the function to the block
											 BlockGraph bg1 = new BriefBlockGraph(mdt1.getActiveBody());
											 List<Block> succBlockList = new ArrayList();
											 List<Block> predBlockList = new ArrayList();
											 predBlockList.add(block);
											 for(Block blks:block.getSuccs())
											 {
												 succBlockList.add(blks);
											 }
											 System.out.println("\nblock successor list before : "+ succBlockList);
											 
										
											 //succBlockList.add(bg1.getBlocks().get(0));   //ORIGINAL
											 //block.setSuccs(succBlockList);               //ORIGINAL
											 
											 System.out.println("\nblock successor list after : "+ succBlockList);
											 System.out.println("\n done...");
											 /*for (Block block1:bg.getBlocks())
											 {
												 for (Block block2:bg1.getBlocks())
												 {
													 System.out.println("\nblock1 :  "+block1.toString());
													 System.out.println("\nblock2 :  "+block2.toString());
													 if(block1.toString().contains(block2.toString()))
													 {
														 System.out.println("\nblock equals : "+block1.toString());
													 }
												 }
											 }*/
											 //adding to the bg
											 /*
											  * public Block(Unit aHead,
             									Unit aTail,
             									Body aBody,
             									int aIndexInMethod,
             									int aBlockLength,
             									BlockGraph aBlockGraph)

    											Constructs a Block in the context of a BlockGraph, and enclosing Body instances.

    											Parameters:
        											aHead - The first unit ir this Block.
        											aTail - The last unit in this Block.
        											aBody - The Block's enclosing Body instance.
        											aIndexInMethod - The index of this Block in the list of Blocks that partition it's enclosing Body instance.
        											BlockLength - The number of units that makeup this block.
        											aBlockGraph - The Graph of Blocks in which this block lives.
											  */
											 Unit aHead = bg1.getBlocks().get(0).getHead();
											 Unit aTail = bg1.getBlocks().get(0).getTail();
											 Body aBody = bg1.getBlocks().get(0).getBody();
											 int aIndexInMethod =currNoBlks++;
											 //currNoBlks = currNoBlks + 1;
											 int aBlockLength = bg1.getBlocks().get(0).getBody().getUnits().size();
											 Block a = new Block (aHead,aTail,aBody,aIndexInMethod,aBlockLength,bg);
											 List <Block> blocksInBG = new ArrayList();
											 for (Block blksInBG :bg.getBlocks() )
											 {
												 blocksInBG.add(blksInBG);
											 }
											 //bg.getBlocks().add(aIndexInMethod, a);
											 succBlockList.add(a); 
											 a.setPreds(predBlockList);
											 System.out.println("\n block a contents : "+a.toString());
											 block.setSuccs(succBlockList); 
											 //bg.addBlocks(a);
											 
											 //*****
											 //DummyBlock head = new DummyBlock(graph.getBody(), 0);
											 a.getBody().getAllUnitBoxes().get(0);
											 
											 /*Iterator stmtIt = block..getUnits().snapshotIterator();
											 stmtIt = bg1.getBody().getUnits().snapshotIterator();
											 while (stmtIt.hasNext())
											 {
												 Stmt s = (Stmt) stmtIt.next();
												 System.out.println("\n s:"+s.toString());
												 s.addBoxPointingToThis(body.getAllUnitBoxes().get(0));
												 break;
											 }
											 List<Block> oldTailList = new ArrayList();
											 oldTailList.add(block);
											 DummyBlock tail = new DummyBlock(bg.getBody(), bg.size());*/
											 //bg.getBody().
											 //*****
											 
											//adding to the bg
											 CFGToDotGraph y = new CFGToDotGraph();
										     DotGraph a1=y.drawCFG(bg,mdt.getActiveBody());
										     a1.plot(mdt.getName()+"333.dot");
										     
										     System.out.println("\n ***Changed CFG***");
										     for (Block blockaftChg:bg.getBlocks())
										     {
										    	 System.out.println(blockaftChg.toString());
										     }
										     System.out.println("\n ***Changed CFG***");
										   
										 }
							    	 }
									
								}
							}
						} catch (IOException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
			
					}
				}
				//we are done with dummymain mdt
				System.out.println("done... ");//only once
				break;
			}
		}
		}
		
	
	public static void mergeCFG7s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{
		int done=0;
		for (String mdtSig:sootMethodsSignatureList) 
		{
			System.out.println("\nmdtSig : "+mdtSig);
			
			for (SootMethod mdt:entryPoint)
			{
				if(mdt.getName().contains("dummyMainMethod"))
				{
					Body body = mdt.retrieveActiveBody();
					BlockGraph bg = new BriefBlockGraph(body);
					for (Block block:bg)
					{
						done=0;
						System.out.println("\nblock content: "+block.toString());
						if (block.toString().contains("invoke"))
						{
							for(Unit unitInBlk:block.getBody().getUnits())
							{
								if (unitInBlk.toString().contains("invoke") && (!unitInBlk.toString().contains("if")))
								{
									for (SootMethod mdt1:entryPoint) 
							    	 {
										 if (mdt1.getSignature().equals(mdtSig))
								    	 {
											 BlockGraph bg1 = new BriefBlockGraph(mdt1.getActiveBody());
											 List<Block> succBlockList = new ArrayList();
											 for(Block blks:block.getSuccs())
											 {
												 succBlockList.add(blks);
											 }
											 //***initial***
											 succBlockList.add(bg1.getBlocks().get(0));
											 block.setSuccs(succBlockList);
											 done=1;
											 break;
											 //***initial***
											 /*for (Block mdt1blk:bg1.getBlocks()) 
											 {
												 System.out.println("\nblks in mdt1:  "+mdt1blk.toString());
											 }*/
								    	 }
							    	 }
									CFGToDotGraph y = new CFGToDotGraph();
							        //DotGraph a=y.drawCFG(x,entryPoint.getActiveBody());//gives units in cfg
							        DotGraph a=y.drawCFG(bg,mdt.getActiveBody());
							        a.plot(mdt.getName()+"333.dot");
								}
								if (done==1)
									break;
							}
						}
					}
					
				}
			}
			//break;
		}
		
	}
	
	public static void mergeCFG6s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{
		for (SootMethod mdt:entryPoint)
		{
			if(mdt.getName().contains("dummyMainMethod"))
			{
				Body body = mdt.retrieveActiveBody();
				BlockGraph bg = new BriefBlockGraph(body);
				for (Block block:bg)
				{
					System.out.println("\nblock content: "+block.toString());
					if (block.toString().contains("invoke"))
					{
						for (String mdtSig:sootMethodsSignatureList) 
						{
							System.out.println("\nmdtSig : "+mdtSig);
							//find out the mdt name
							//find the units of the block
							List<Unit>unitsInBlkList = new ArrayList();
							for(Unit unitInBlk:block.getBody().getUnits())
							{
								if (unitInBlk.toString().contains("invoke") && (!block.toString().contains("if")))
								{
									System.out.println("\nUnit To String Content outside if: "+unitInBlk.toString());
									//chk if any unit satisfies the condition
									if (unitInBlk.toString().contains(mdtSig))
									{
										System.out.println("\nUnit To String Content inside if: "+unitInBlk.toString());
										//get the cfg of the function to insert in unitchain
										 for (SootMethod mdt1:entryPoint) 
								    	 {
											 if (mdt1.getSignature().equals(mdtSig))
									    	 {
												 BlockGraph bg1 = new BriefBlockGraph(mdt1.getActiveBody());
												 List<Block> succBlockList = new ArrayList();
												 for(Block blks:block.getSuccs())
												 {
													 succBlockList.add(blks);
												 }
												 //***initial***
												 succBlockList.add(bg1.getBlocks().get(0));
												 block.setSuccs(succBlockList);
												 break;
												 //***initial***
												 /*for (Block mdt1blk:bg1.getBlocks()) 
												 {
													 System.out.println("\nblks in mdt1:  "+mdt1blk.toString());
												 }*/
									    	 }
								    	 }
									}
									break;
								}
								//unitsInBlkList.add(unitInBlk);
							}
						}
					}
				}
				//BlockGraph bg = new BriefBlockGraph(body);
				CFGToDotGraph y = new CFGToDotGraph();
		        //DotGraph a=y.drawCFG(x,entryPoint.getActiveBody());//gives units in cfg
		        DotGraph a=y.drawCFG(bg,mdt.getActiveBody());
		        a.plot(mdt.getName()+"333.dot");
			}
		}
	}
	
	public static void mergeCFG5s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{
		for (SootMethod mdt:entryPoint)
		{
			if(mdt.getName().contains("dummyMainMethod"))
			{
				Body body = mdt.retrieveActiveBody();
				BlockGraph bg = new BriefBlockGraph(body);
				for (Block block:bg)
				{
					System.out.println("\nblock content: "+block.toString());
					if (block.toString().contains("invoke") && (!block.toString().contains("if")))
					{
						for (String mdtSig:sootMethodsSignatureList) 
						{
							//find out the mdt name
							if (block.toString().contains(mdtSig))
							{
								System.out.println("B4: index of this block : " + block.getIndexInMethod());
								//System.out.println("B4: successors : " + succBlockIdxList);
								//get the cfg of the function to insert in unitchain
								 for (SootMethod mdt1:entryPoint) 
						    	 {
									 if (mdt1.getSignature().equals(mdtSig))
							    	 {
										 BlockGraph bg1 = new BriefBlockGraph(mdt1.getActiveBody());
										 List<Block> succBlockList = new ArrayList();
										 for(Block blks:block.getSuccs())
										 {
											 succBlockList.add(blks);
										 }
										 succBlockList.add(bg1.getBlocks().get(0));
										 block.setSuccs(succBlockList);
							    	 }
						    	 }
							}
						}
					}
					
				}
				//BlockGraph bg = new BriefBlockGraph(body);
				CFGToDotGraph y = new CFGToDotGraph();
		        //DotGraph a=y.drawCFG(x,entryPoint.getActiveBody());//gives units in cfg
		        DotGraph a=y.drawCFG(bg,mdt.getActiveBody());
		        
		        a.plot(mdt.getName()+"333.dot");
			}
		}
		
		
		
	}
	
	public static void mergeCFG4s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{
		for (SootMethod mdt:entryPoint)
		{
			if(mdt.getName().contains("dummyMainMethod"))
			{
				Body body = mdt.retrieveActiveBody();
				BlockGraph bg = new BriefBlockGraph(body);
				for (Block block:bg)
				{
					System.out.println("\nblock content: "+block.toString());
					//get the list of successors for this block
					List<Block> succBlockList = block.getSuccs();
					List<Integer>succBlockIdxList = new ArrayList();
					
					List<Block> succBlockListAfter = block.getSuccs();
					List<Integer>succBlockIdxListAfter = new ArrayList();
					for(Block eachSuccessor:succBlockList)
					{
						succBlockIdxList.add(eachSuccessor.getIndexInMethod());
					}
					
					if (block.toString().contains("invoke") && (!block.toString().contains("if")))
					{
						for (String mdtSig:sootMethodsSignatureList) 
						{
							//find out the mdt name
							if (block.toString().contains(mdtSig))
							{
								System.out.println("B4: index of this block : " + block.getIndexInMethod());
								System.out.println("B4: successors : " + succBlockIdxList);
								//get the cfg of the function to insert in unitchain
								 for (SootMethod mdt1:entryPoint) 
						    	 {
									 if (mdt1.getSignature().equals(mdtSig))
							    	 {
							    		//get the blockgraph
										System.out.println("mdtsig  : " + mdtSig.toString());
										Body body1 = mdt1.retrieveActiveBody();
										BlockGraph bg1 = new BriefBlockGraph(body1);
										//bg.getBlocks().get(block.getIndexInMethod()).setSuccs(bg1.getBlocks());//setting allblocks of cfg as successors
										//bg.getBlocks().get(block.getIndexInMethod()).getBody().getUnits().insertAfter(mdt1.getActiveBody().getUnits(), block.getTail());//cause error
										//******//
										//$$$$$$//
										//look inside each of the units in the blocks
										PatchingChain<Unit> unitsInBlock = block.getBody().getUnits();
										Iterator<Unit> unitInBlk = block.iterator();
										System.out.println("content in unit in block : "+ block.toString());
										while(unitInBlk.hasNext())
										{
											Unit nextUnit = unitInBlk.next();
											Unit nextNextUnit = unitInBlk.next();
											Unit lastUnit = block.getTail();
											//Unit cloneNexUnit = (Unit) nextUnit.clone();
											System.out.println("content in unit in block11111 : "+ nextUnit.toString());
											if (nextUnit.toString().contains(mdtSig))
											{
												//mdt.getActiveBody().getUnits().insertAfter(mdt1.getActiveBody().getUnits(),nextUnit);
												//mdt.getActiveBody().getUnits().insertAfter(mdt1.getActiveBody().getUnits(),lastUnit);
											}
											break;
										}
										//now...lets connect the blocks together..make the block connection
										BlockGraph newMdtBg = new BriefBlockGraph(mdt1.getActiveBody());
										for (Block eachNewBlk:newMdtBg.getBlocks())
										{
											System.out.println("content in eachNewBlk in block : "+ eachNewBlk.toString());
											System.out.println("looking for mdt sig : "+ mdtSig);
											//if (eachNewBlk.toString().contains(mdtSig))
											//{
												System.out.println("content in eachNewBlk in block : "+ eachNewBlk.toString());
												List<Block>beforeSuccList = new ArrayList();
												for (Block eachOldSuccBlk:block.getSuccs())
													beforeSuccList.add(eachOldSuccBlk);
												beforeSuccList.add(eachNewBlk);
												block.setSuccs(beforeSuccList);
												List<Block>beforepredecessorList = new ArrayList();
												beforepredecessorList.add(block);
												eachNewBlk.setPreds(beforepredecessorList);
											//}
										}
										//now...lets connect the blocks together..make the block connection
										
										/*for (Unit unitInBlk:unitsInBlock)
										{
											System.out.println("content in unit in block : "+ unitInBlk.toString());
										}*/
										//$$$$$$//
										//the second arguement unit is wrong...
										//mdt.getActiveBody().getUnits().insertAfter(mdt1.getActiveBody().getUnits(),block.getBody().getUnits().getFirst());
										block.setSuccs(succBlockList);//adding in successors again
										Body newBody = mdt.retrieveActiveBody();
										BlockGraph mdtBg = new BriefBlockGraph(newBody);
										DirectedGraph<Unit> x = new ExceptionalUnitGraph(mdt.getActiveBody());
										//System.out.println("first unit in block : " + block.getBody().getUnits().getFirst().toString());
										//******//
										
										CFGToDotGraph y = new CFGToDotGraph();
								        //DotGraph a=y.drawCFG(x,entryPoint.getActiveBody()); //gives units in cfg
										//clear the successor list for this block
										List<Block>emptySuccList = new ArrayList();
										block.setSuccs(emptySuccList);
								        DotGraph a=y.drawCFG(mdtBg,mdt.getActiveBody());
								        a.plot(mdt.getName()+"222.dot");
								        //add back in
								        //block.setSuccs(succBlockListAfter);
								        
								        //find the successor blocks after the merger
								        succBlockListAfter = block.getSuccs();
								        for(Block eachSuccessorAfter:succBlockListAfter)
										{
								        	succBlockIdxListAfter.add(eachSuccessorAfter.getIndexInMethod());
										}
								        System.out.println("After: index of this block : " + block.getIndexInMethod());
								        System.out.println("block string content"  + block.toString());
								        System.out.println("After: index of this block : " + block.getIndexInMethod());
										System.out.println("After: predecessors : " + block.getPreds());
										System.out.println("After: successors : " + block.getSuccs());
										System.out.println("Merging done");
								        //return;
							    	 }
						    	 }
								//add the cfg of the function after this block
								//block.getBody().getUnits().insertAfter(toInsert, point);
							}
						}
					}
				}
			}
		}
	}
	
	public static void mergeCFG3s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
	{
		for (SootMethod mdt:entryPoint)
		{
			if(mdt.getName().contains("dummyMainMethod"))
			{
				Body body = mdt.retrieveActiveBody();
				BlockGraph bg = new BriefBlockGraph(body);
				for (Block block:bg)
				{
					 PatchingChain<Unit> allUnitsInBlock = body.getUnits();block.getBody().getUnits();
					 for (Unit eachunit:allUnitsInBlock)
					 {
						 if (eachunit.toString().contains("invoke") && (!eachunit.toString().contains("if")))
						 {
							 for (String mdtSig:sootMethodsSignatureList) 
							 {
								 if (eachunit.toString().contains(mdtSig))
					    		{
									 List<Integer>successorBlksId =new ArrayList();
									 //this block contains the unit that calls the function
									 //so get the successors of this block
									 List<Block> successorList = block.getSuccs();
									 for (Block eachSuccBlk:successorList)
									 {
										 successorBlksId.add(eachSuccBlk.getIndexInMethod());
									 }
									 //add each of the id of the successors to the successor
					    		}
								 for (SootMethod mdt1:entryPoint) 
					    		{
									if(mdt1.getActiveBody().getAllUnitBoxes().size()>0)//remove later
									{
						    			if (mdt1.getSignature().equals(mdtSig))
						    			{
						    				System.out.println("dummy UnitToString  : " + eachunit.toString());
				    						System.out.println("Method unit to Signature : " + mdt1.getSignature() +"\n");
				    						mdt.getActiveBody().getUnits().insertAfter(mdt1.retrieveActiveBody().getUnits(),eachunit);
						    			}
						    			
									}
					    		}
							 }//end of sootMethodsSignatureList
							 //add in the cfg here
							 
						 }//
					 }
				}

			}
			generateCFG111 (mdt);//this works bt loop is stuck
		}
	}
	
	//Function added in to generate the CFG
    public static void mergeCFG1s (List <SootMethod> entryPoint, List <String> sootMethodsSignatureList)
    {	
    	for (SootMethod mdt:entryPoint)
    	{
    		if(mdt.getName().contains("dummyMainMethod"))
			{
    			Body body = mdt.retrieveActiveBody();
    			
    			
			    //Build CFG
			    UnitGraph cfg = new ExceptionalUnitGraph(body);
			    PatchingChain<Unit> allunits = body.getUnits();
			    for (Unit eachunit:allunits) 
			    {
			    	//System.out.println("unitToString : "+eachunit.toString()+"\n");
			    	if (eachunit.toString().contains("invoke") && (!eachunit.toString().contains("if")))
			    	{
			    		
			    		for (String mdtSig:sootMethodsSignatureList) 
			    		{
			    			if (eachunit.toString().contains(mdtSig))
			    			{
			    				//get successor of this unit
			    				Unit successor = mdt.retrieveActiveBody().getUnits().getSuccOf(eachunit);
			    				
			    				//System.out.println("UnitToString  : " + eachunit.toString());
			    				//System.out.println("Method Signature : " + mdtSig +"\n");
			    				//look for the sootmethod cfg for this function
			    				//then merge it with the unit that invokes this call
			    				for (SootMethod mdt1:entryPoint) 
			    				{
			    					if (mdt1.getSignature().equals(mdtSig))
			    					{
			    						System.out.println("dummy UnitToString  : " + eachunit.toString());
			    						System.out.println("Method unit to Signature : " + mdt1.getSignature() +"\n");
			    						//***merge here... merge the unit - mdt(dummymain) and the mdt1 tog***
			    						//***added in***
			    						//mdt.getActiveBody().getUnits().insertAfter(mdt1.retrieveActiveBody().getUnits(),eachunit);//works
			    						//generateCFG111 (mdt);
			    						//break; //only do init mainActivity
			    						//***added in***
			    						if(mdt1.getActiveBody().getAllUnitBoxes().size()>0)
			    						{
			    							//found the sootmdt
			    							System.out.println("\n"+"*****unitboxes > 1*****");
			    							System.out.println("dummy UnitToString  : " + eachunit.toString());
				    						System.out.println("Method unit to Signature : " + mdt1.getSignature());
				    						System.out.println("Mdt1.activebody to string : " + mdt1.getActiveBody().getAllUnitBoxes().get(0).toString());
				    						//System.out.println("Mdt1.activebody to string : " + mdt1.getActiveBody().getUnits().);
				    						System.out.println("*****unitboxes > 1*****"+"\n");
			    							eachunit.addBoxPointingToThis(mdt1.getActiveBody().getAllUnitBoxes().get(0));
			    							//mdt.getActiveBody().getUnits().insertAfter(mdt1.getActiveBody().getUnits(),eachunit); //error
			    							List<Unit> lastUnitsList=getLastUnitsSootMethod (mdt1);
			    							System.out.println("*last unit*  : " + lastUnitsList.toString());//last units in the function cfg
			    							
			    							Unit dupUnit = eachunit;
			    							//mdt.getActiveBody().getUnits().insertOnEdge(mdt1.retrieveActiveBody().getUnits(), dupUnit, successor);
			    							//make a link between block 6 and 7
			    							
			    							//mdt.getActiveBody().getUnits().insertAfter(mdt1.retrieveActiveBody().getUnits(),dupUnit);//works
			    							
			    							/*UnitBox predecessorUB = Jimple.v().newStmtBox(null);
			    							if (predecessorUB.canContainUnit(dupUnit))
	    						    		{
	    						    			predecessorUB.setUnit(dupUnit);
	    						    		}
			    							UnitBox successorUB = Jimple.v().newStmtBox(null);
			    							if (successorUB.canContainUnit(successor))
	    						    		{
			    								successorUB.setUnit(successor);
	    						    		}
			    							dupUnit.addBoxPointingToThis(successorUB);*/
			    							
			    							//mdt.getActiveBody().getUnits().insertOnEdge(mdt1.retrieveActiveBody().getUnits(),eachunit, successor);//same as above
			    							//mdt.getActiveBody().getUnits().insertBefore(mdt1.retrieveActiveBody().getUnits(),successor);
			    							
			    							//look for the last units of mdt1(the inserted cfg) in the merged cfg
			    							//PatchingChain<Unit> mergedCfgUnits = mdt.retrieveActiveBody().getUnits();
			    						    /*for (Unit eachMergedUnit:mergedCfgUnits) 
			    						    {
			    						    	for (Unit initialLastUnit:lastUnitsList)
			    						    	{
			    						    		UnitBox lastUnitInMergedCFG = Jimple.v().newStmtBox(null);
			    						    		if (lastUnitInMergedCFG.canContainUnit(initialLastUnit))
			    						    		{
			    						    			System.out.println("returns true...");
			    						    			lastUnitInMergedCFG.setUnit(initialLastUnit);
			    						    		}
			    						    		if (eachMergedUnit.equals(initialLastUnit))
			    						    		{
			    						    			System.out.println("***"+eachMergedUnit.toString()+"***");
			    						    			List <UnitBox> a=mdt.getActiveBody().getUnitBoxes(true);//gets unitbooxes
			    						    			for (UnitBox newUnitBoxes:a)
			    						    			{
			    						    				System.out.println("*****newunitboxunit:"+newUnitBoxes.getUnit().toString()+"*****");
			    						    				System.out.println("*****successor:"+successor.toString()+"*****");
			    						    				
			    						    				if(newUnitBoxes.getUnit().toString().equals(successor.toString()))
			    						    				{
			    						    					System.out.println("successor same content...");
			    						    					//create link between each eachMergedUnit(initialLastUnit) and the unit in this newUnitBox
			    						    					newUnitBoxes.getUnit().addBoxPointingToThis(lastUnitInMergedCFG);
			    						    					
			    						    		
			    						    				}
			    						    				//eachMergedUnit.addBoxPointingToThis(initialLastUnit1);
			    						    				mdt.getActiveBody().getUnits().insertBefore(mdt1.retrieveActiveBody().getUnits(),initialLastUnit);//works
			    						    			}
			    						    			//System.out.println("***"+a.toString()+"***");
			    						    			
			    						    		}
			    						    	}
			    						    }*/
			    							
			    							
			    							//then merge the successor to the two last units
			    							
			    							generateCFG111 (mdt);//this works bt loop is stuck
			    						}
			    						
			    					   //***merge here... merge the unit - eachnuit and the mdt1 tog***
			    					}
			    				}
			    			}
			    		}
			    	}
			    }
			    generateCFG111 (mdt);
			    break;
			}//if cond ends here
    	}//end of biggest for loop
    	//construct the graph again for the changed body
    }
	
    //Function added in to generate the CFG
    //This function will return the list of units that have no successors
    public static List<Unit> getLastUnitsSootMethod (SootMethod method)
    {
    	
    	System.out.println("*****getLastUnitsSootMethod***** ");
    	List<Unit> lastUnitsList =new ArrayList<Unit>();
    	PatchingChain<Unit> allunits = method.retrieveActiveBody().getUnits();
	    for (Unit eachunit:allunits) 
	    {
	    	//Unit successor = method.retrieveActiveBody().getUnits().getSuccOf(eachunit);
	    	//if(eachunit.toString().contains("return") && successor!=null)
	    	if(eachunit.toString().contains("return") )
	    	{
	    		//System.out.println("last unit: "+eachunit.toString());
	    		lastUnitsList.add(eachunit);
	    	}
	    }
	    //System.out.println("last units:"+lastUnitsList);
	    System.out.println("*****getLastUnitsSootMethod***** ");
	    return lastUnitsList;
    }
	
	//Function added in to generate the CFG
	public static void mergeCFGs (List <SootMethod> entryPoint, List <String> sootMethodNames)
	{
		//look through the list of SootMethod objects and get the one with the dummymain as name
		for (SootMethod mdt:entryPoint)
		{
			if(mdt.getName().contains("dummyMainMethod"))
			{
				Body body = mdt.retrieveActiveBody();
			    //Build CFG
			    UnitGraph cfg = new ExceptionalUnitGraph(body);
			    PatchingChain<Unit> allunits = body.getUnits();
			    for (Unit eachunit:allunits) 
			    {
			    	System.out.println("unitToString : "+eachunit.toString()+"\n");
			    	if (eachunit.toString().contains("invoke") && (!eachunit.toString().contains("if")))
			    	{
				    	//find the exact mdt name
				    	String array1[]= eachunit.toString().split(":");
		    			String array2[]= array1[1].split(" ");
		    			//continue here...
		    			if (array2[2].contains("("))
		    			{
		    				//array1= array2[2].toString().split("(");
		    				array1=array2[2].toString().split("\\(");
		    				//System.out.println("string parts: "+ array1[0]+"\n");
		    				
		    			}
		    			//System.out.println("string parts: "+ array2[2]+"\n");
		    			//System.out.println("each unit to string: "+eachunit+"\n");
		    			for (String mdtName:sootMethodNames)
		    			{
		    				if (array1[0].equals(mdtName))
		    				{
		    					//System.out.println("mdtNamelll : "+ mdtName+"\n");
		    					System.out.println("eachunuitllll : "+eachunit.toString()+"\n");
		    					//find the sootmethod with this name
		    					for (SootMethod thismdt:entryPoint)
		    					{
		    						if (thismdt.getName().equals(mdtName))
		    						{
		    							System.out.println("mdtNamellllll : "+ thismdt.getName()+"\n");
		    						}
		    					}
		    					
		    				}
		    			}
		    			//System.out.println(mdtName+" merge CFG here..."+"\n");
				    	
				    	//find the exact mdt name
			    	}
			    	/*for (String mdtName:sootMethodNames)
			    	{
			    		
			    		if (eachunit.toString().contains(mdtName) && (!eachunit.toString().contains("if")))
			    		{
			    			String array1[]= eachunit.toString().split(":");
			    			String array2[]= array1[1].split(" ");
			    			//continue here...
			    			if (array2[2].contains("("))
			    			{
			    				//array1= array2[2].toString().split("(");
			    				array1=array2[2].toString().split("\\(");
			    				System.out.println("string parts: "+ array1[0]+"\n");
			    				
			    			}
			    			//System.out.println("string parts: "+ array2[2]+"\n");
			    			System.out.println("each unit to string: "+eachunit+"\n");
			    			System.out.println(mdtName+" merge CFG here..."+"\n");
			    		}
			    	}*/
				}
			}
			else
			{
				System.out.println("else path...mdt.getName() is "+mdt.getName()+"\n");
			}
		}
		//look for the units inside this object
		//if any of the units contain a call for any other sootMethod, thenmerge the unit with the entryPoint object
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
		
	   //*****added in code3*****
		PackManager.v().getPack("cg").apply(); //this works
	    CallGraph appCallGraph = Scene.v().getCallGraph();
	   
	    File graph =serializeCallGraph(appCallGraph, "callgraph");//for CallGraph
	    
		System.out.println("done done done111...");
		String androidPlatformPath = "/home/shaila/Android/Sdk/platforms";
	    //String appPath = "/home/shaila/Desktop/flowdroid2/soot-infoflow-android-develop/insecureBank/InsecureBank.apk";
		//String appPath = "/home/shaila/Desktop/NewAPKs2/Broadcast/BroadcastReceiver/OriginalAPK/BroadcastReceiverNewSms-debug.apk";
		String appPath = "/home/shaila/Desktop/NewAPKs2/ServiceComponent/OriginalAPK/ServiceOriginalApk.apk";
		SetupApplication app = new SetupApplication(androidPlatformPath,appPath);
		try {
			app.runInfoflow("/home/shaila/Desktop/flowdroid2/soot-infoflow-android-develop/SourcesAndSinks.txt");
		} 
		catch (XmlPullParserException e) {
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
        
        SootMethod entryPoint = app.getDummyMainMethod();
        sootMethodsObjectList.add(entryPoint);
 	    Options.v().set_main_class(entryPoint.getSignature());
 	    Scene.v().setEntryPoints(Collections.singletonList(entryPoint));
 	    System.out.println("hhhh");
 	    System.out.println(entryPoint.getActiveBody());
 	    
 	    //getting the CFG of the DummyMainMethod
 	    generateCFG (entryPoint);
 	    
 	    //getting the entrypoint classes from the DummyMainMethod
 	    Set <SootClass> entryPoint1 =  app.getEntrypointClasses();
	    System.out.println(entryPoint1);
	    for (SootClass eachentrypt:entryPoint1){
		    List <SootMethod> mdtsInSootClass = eachentrypt.getMethods();
		    System.out.println("\n"+eachentrypt.toString()+" "+eachentrypt.getMethods().toString());
		    //get the all the methods in these classes, get the CFGs for those classes
		    for(SootMethod  mdt : mdtsInSootClass)
		    {    
		    	 generateCFG (mdt);
		         sootMethodsNameList.add(mdt.getName());
		         sootMethodsObjectList.add(mdt);
		         sootMethodsSignatureList.add(mdt.getSignature());
		     	 sootMethodsSubSignatureList.add(mdt.getSubSignature());
		        
		         //trying to generate the ExceptionalUnitGraph
		         /*DirectedGraph<Unit> x = new ExceptionalUnitGraph(mdt.getActiveBody());
		         CFGToDotGraph y = new CFGToDotGraph();
		         DotGraph a=y.drawCFG(x,mdt.getActiveBody());
		         a.plot("cfg.dot");*/ 
		    }
	    }
	    System.out.println("mergeCFGs () function called No1 ....");
	    //mergeCFGs (sootMethodsObjectList, sootMethodsNameList);
	    //addingDummyTail(sootMethodsObjectList, sootMethodsSignatureList);
	    mergeCFG101s (sootMethodsObjectList, sootMethodsSignatureList);
	    
	    System.out.println("sootMethodsObjectList: " + sootMethodsObjectList);
	    System.out.println("sootMethodsNameList: " + sootMethodsNameList);
	    System.out.println("sootMethodsSignatureList: " + sootMethodsSignatureList);
	    //System.out.println("sootMethodsSubSignatureList: " + sootMethodsSubSignatureList);
		//getting the callgraph
		
	   //*****added in code3***** 
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

class DummyBlock extends Block
{
    DummyBlock(Body body, int indexInMethod)
    {
        super(null, null, body, indexInMethod, 0, null);
    }

    void makeHeadBlock(List<Block> oldHeads)
    {
        setPreds(new ArrayList<Block>());
        setSuccs(new ArrayList<Block>(oldHeads));

        Iterator<Block> headsIt = oldHeads.iterator();
        while(headsIt.hasNext()){
            Block oldHead = headsIt.next();

            List<Block> newPreds = new ArrayList<Block>();
            newPreds.add(this);

            List<Block> oldPreds = oldHead.getPreds();
            if(oldPreds != null)
                newPreds.addAll(oldPreds);
            
            oldHead.setPreds(newPreds);
        }
    }

    void makeTailBlock(List<Block> oldTails)
    {
        setSuccs(new ArrayList<Block>());
        setPreds(new ArrayList<Block>(oldTails));

        Iterator<Block> tailsIt = oldTails.iterator();
        while(tailsIt.hasNext()){
            Block oldTail = tailsIt.next();

            List<Block> newSuccs = new ArrayList<Block>();
            newSuccs.add(this);

            List<Block> oldSuccs = oldTail.getSuccs();
            if(oldSuccs != null)
                newSuccs.addAll(oldSuccs);

            oldTail.setSuccs(newSuccs);
        }
    }    
    
    public Iterator<Unit> iterator()
    {
        return Collections.emptyListIterator();
    }
}

