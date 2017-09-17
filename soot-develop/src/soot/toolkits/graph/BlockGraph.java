/* Soot - a J*va Optimization Framework
 * Copyright (C) 1999 Patrice Pominville, Raja Vallee-Rai
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the
 * Free Software Foundation, Inc., 59 Temple Place - Suite 330,
 * Boston, MA 02111-1307, USA.
 */

/*
 * Modified by the Sable Research Group and others 1997-2003.  
 * See the 'credits' file distributed with Soot for the complete list of
 * contributors.  (Soot is distributed at http://www.sable.mcgill.ca/soot)
 */

package soot.toolkits.graph;

import java.util.*;

import soot.*;
import soot.jimple.Jimple;
import soot.jimple.NopStmt;
import soot.jimple.Stmt;
import soot.tagkit.StringTag;
import soot.tagkit.Tag;
import soot.util.Chain;

/**
 * <p>
 * Represents the control flow graph of a {@link Body} at the basic block level.
 * Each node of the graph is a {@link Block} while the edges represent the flow
 * of control from one basic block to the next.
 * </p>
 *
 * <p>
 * This is an abstract base class for different variants of {@link BlockGraph},
 * where the variants differ in how they analyze the control flow between
 * individual units (represented by passing different variants of
 * {@link UnitGraph} to the <code>BlockGraph</code> constructor) and in how they
 * identify block leaders (represented by overriding <code>BlockGraph</code>'s
 * definition of {@link computeLeaders()}.
 */
public abstract class BlockGraph implements DirectedGraph<Block> {
	protected Body mBody;
	protected Chain<Unit> mUnits;
	protected List<Block> mBlocks;
	protected List<Block> mHeads = new ArrayList<Block>();
	protected List<Block> mTails = new ArrayList<Block>();
	//create Map to hold that unit and its successor unit
	protected Map<Unit, List<Block>> tailToSuccsMap =new HashMap<Unit, List<Block>>();

	/**
	 * Create a <code>BlockGraph</code> representing at the basic block level
	 * the control flow specified, at the <code>Unit</code> level, by a given
	 * {@link UnitGraph}.
	 *
	 * @param b
	 *            A representation of the control flow at the level of
	 *            individual {@link Unit}s.
	 */
	//parameter Unit succUnit was added in
	protected BlockGraph(UnitGraph b) {
		mBody = b.getBody();
		mUnits = mBody.getUnits();
		for (Unit eachUnit:b.getBody().getUnits())
		 {
			 if(eachUnit.getTags().size()>0)
			 {
				 Tag tagVal2 = eachUnit.getTags().get(eachUnit.getTags().size()-1);
				 if(tagVal2.toString().equals("successor"))
				 {
					 System.out.println("7.successor found : "+eachUnit.toString());
					 System.out.println("7.successor tags : "+eachUnit.getTags().toString());
				 }
			 }
		 }
		Set<Unit> leaders = computeLeaders(b);
		buildBlocks(leaders, b);
	}

	/**
	 * <p>
	 * Utility method for computing the basic block leaders for a {@link Body},
	 * given its {@link UnitGraph} (i.e., the instructions which begin new basic
	 * blocks).
	 * </p>
	 *
	 * <p>
	 * This implementation designates as basic block leaders :
	 *
	 * <ul>
	 *
	 * <li>Any <code>Unit</code> which has zero predecessors (e.g. the
	 * <code>Unit</code> following a return or unconditional branch) or more
	 * than one predecessor (e.g. a merge point).</li>
	 *
	 * <li><code>Unit</code>s which are the target of any branch (even if they
	 * have no other predecessors and the branch has no other successors, which
	 * is possible for the targets of unconditional branches or degenerate
	 * conditional branches which both branch and fall through to the same
	 * <code>Unit</code>).</li>
	 *
	 * <li>All successors of any <code>Unit</code> which has more than one
	 * successor (this includes the successors of <code>Unit</code>s which may
	 * throw an exception that gets caught within the <code>Body</code>, as well
	 * the successors of conditional branches).</li>
	 *
	 * <li>The first <code>Unit</code> in any <code>Trap</code> handler.
	 * (Strictly speaking, if <code>unitGraph</code> were a
	 * <code>ExceptionalUnitGraph</code> that included only a single
	 * unexceptional predecessor for some handler&mdash;because no trapped unit
	 * could possibly throw the exception that the handler catches, while the
	 * code preceding the handler fell through to the handler's code&mdash;then
	 * you could merge the handler into the predecessor's basic block; but such
	 * situations occur only in carefully contrived bytecode.)
	 *
	 * </ul>
	 * </p>
	 *
	 * @param unitGraph
	 *            is the <code>Unit</code>-level CFG which is to be split into
	 *            basic blocks.
	 *
	 * @return the {@link Set} of {@link Unit}s in <code>unitGraph</code> which
	 *         are block leaders.
	 */
	protected Set<Unit> computeLeaders(UnitGraph unitGraph) {
		Body body = unitGraph.getBody();
		if (body != mBody) {
			throw new RuntimeException(
					"BlockGraph.computeLeaders() called with a UnitGraph that doesn't match its mBody.");
		}
		Set<Unit> leaders = new HashSet<Unit>();

		// Trap handlers start new basic blocks, no matter how many
		// predecessors they have.
		for (Unit eachUnit:mBody.getUnits())
		{
			 if(eachUnit.getTags().size()>0)
			 {
				 Tag tagVal2 = eachUnit.getTags().get(eachUnit.getTags().size()-1);
				 if(tagVal2.toString().equals("successor"))
				 {
					 System.out.println("8.successor found : "+eachUnit.toString());
					 System.out.println("8.successor tags : "+eachUnit.getTags().toString());
				 }
			 }
		 }
		Chain<Trap> traps = body.getTraps();
		for (Iterator<Trap> trapIt = traps.iterator(); trapIt.hasNext();) {
			Trap trap = trapIt.next();
			leaders.add(trap.getHandlerUnit());
		}
		for (Unit eachUnit:mBody.getUnits())
		{
			 if(eachUnit.getTags().size()>0)
			 {
				 Tag tagVal2 = eachUnit.getTags().get(eachUnit.getTags().size()-1);
				 if(tagVal2.toString().equals("successor"))
				 {
					 System.out.println("9.successor found : "+eachUnit.toString());
					 System.out.println("9.successor tags : "+eachUnit.getTags().toString());
				 }
			 }
		 }
		for (Iterator<Unit> unitIt = body.getUnits().iterator(); unitIt.hasNext();) {
			Unit u = unitIt.next();
			List<Unit> predecessors = unitGraph.getPredsOf(u);
			int predCount = predecessors.size();
			List<Unit> successors = unitGraph.getSuccsOf(u);
			int succCount = successors.size();
	
			//Added in
			for (Unit pred:unitGraph.getPredsOf(u))
			{
				if (pred.toString().equals("nop"))
				{
					leaders.add(u);
				}
			}
			//Added in

			if (predCount != 1) { // If predCount == 1 but the predecessor
				leaders.add(u); // is a branch, u will get added by that
			} // branch's successor test.
			if ((succCount > 1) || (u.branches())) {
				for (Iterator<Unit> it = successors.iterator(); it.hasNext();) {
					leaders.add((Unit) it.next()); // The cast is an
				} // assertion check.
			}
		}
		for (Unit eachUnit:mBody.getUnits())
		{
			 if(eachUnit.getTags().size()>0)
			 {
				 Tag tagVal2 = eachUnit.getTags().get(eachUnit.getTags().size()-1);
				 if(tagVal2.toString().equals("successor"))
				 {
					 System.out.println("10.successor found : "+eachUnit.toString());
					 System.out.println("10.successor tags : "+eachUnit.getTags().toString());
				 }
			 }
		 }
		return leaders;
	}

	/**
	 * <p>
	 * A utility method that does most of the work of constructing basic blocks,
	 * once the set of block leaders has been determined, and which designates
	 * the heads and tails of the graph.
	 * </p>
	 *
	 * <p>
	 * <code>BlockGraph</code> provides an implementation of
	 * <code>buildBlocks()</code> which splits the {@link Unit}s in
	 * <code>unitGraph</code> so that each <code>Unit</code> in the passed set
	 * of block leaders is the first unit in a block. It defines as heads the
	 * blocks which begin with <code>Unit</code>s which are heads in
	 * <code>unitGraph</code>, and defines as tails the blocks which end with
	 * <code>Unit</code>s which are tails in <code>unitGraph</code>. Subclasses
	 * might override this behavior.
	 *
	 * @param leaders
	 *            Contains <code>Unit</code>s which are to be block leaders.
	 *
	 * @param unitGraph
	 *            Provides information about the predecessors and successors of
	 *            each <code>Unit</code> in the <code>Body</code>, for
	 *            determining the predecessors and successors of each created
	 *            {@link Block}.
	 *
	 * @return a {@link Map} from {@link Unit}s which begin or end a block to
	 *         the block which contains them.
	 */
	protected Map<Unit, Block> buildBlocks(Set<Unit> leaders, UnitGraph unitGraph) {
		List<Block> blockList = new ArrayList<Block>(leaders.size());
		Map<Unit, Block> unitToBlock = new HashMap<Unit, Block>(); // Maps head															// and tail
		//added in
		int succ_added =0;
		//added in	
		
		// units to
		// their blocks, for building
		// predecessor and successor lists.
		Unit blockHead = null;
		int blockLength = 0;
		Iterator<Unit> unitIt = mUnits.iterator();
		if (unitIt.hasNext()) {
			blockHead = unitIt.next();
			if (!leaders.contains(blockHead)) {
				throw new RuntimeException("BlockGraph: first unit not a leader!");
			}
			blockLength++;
		}
		for (Unit eachUnit:mBody.getUnits())
		{
			 if(eachUnit.getTags().size()>0)
			 {
				 Tag tagVal2 = eachUnit.getTags().get(eachUnit.getTags().size()-1);
				 if(tagVal2.toString().equals("successor") && blockList.size()==74)
				 {
					 System.out.println("11.successor found : "+eachUnit.toString());
					 System.out.println("11.successor tags : "+eachUnit.getTags().toString());
				 }
			 }
		 }
		Unit blockTail = blockHead;
		int indexInMethod = 0;

		while (unitIt.hasNext()) {
			Unit u = unitIt.next();
			//debug
			if(u.getTags().size()>0)
			{
				 Tag tagVal2 = u.getTags().get(u.getTags().size()-1);
				 if(tagVal2.toString().equals("successor"))
				 {
					 //if(u.toString().equals("nop") && u.getTags().toString().equals("[oldtail_3, successor]"))
					 //{
						 System.out.println("11.successor found : "+u.toString());
						 System.out.println("11.successor tags : "+u.getTags().toString()); 
					 //}
				 }
			}
			//debug
			if (leaders.contains(u)) {
				//*****Added In*****
				int added=addBlock(blockHead, blockTail, indexInMethod, blockLength, blockList, unitToBlock);
				if(u.getTags().size()>0)
				{
					 Tag tagVal2 = u.getTags().get(u.getTags().size()-1);
					 if(tagVal2.toString().equals("successor"))
					 {
						 
							 System.out.println("11.1.successor found : "+u.toString());
							 System.out.println("11.1.successor tags : "+u.getTags().toString()); 
					 }
					 System.out.println("11.1.added... : "+added); 
				}
				if(added == 0 )
					--indexInMethod; 
				//*****Added In*****
				indexInMethod++;
				blockHead = u;
				blockLength = 0;
			}
			blockTail = u;
			blockLength++;
		}
		for (Unit eachUnit:mBody.getUnits())
		{
			 if(eachUnit.getTags().size()>0)
			 {
				 Tag tagVal2 = eachUnit.getTags().get(eachUnit.getTags().size()-1);
				 if(tagVal2.toString().equals("successor"))
				 {
					 System.out.println("12.successor found : "+eachUnit.toString());
					 System.out.println("12.successor tags : "+eachUnit.getTags().toString());
					 //Block successorBlk = unitToBlock.get(eachUnit);
					 //System.out.println("12.successorBlk : "+successorBlk.toString());
				 }
			 }
		 }
		if (blockLength > 0) {
			// Add final block.
			addBlock(blockHead, blockTail, indexInMethod, blockLength, blockList, unitToBlock);
		}

		// The underlying UnitGraph defines heads and tails.
		/*for (Iterator<Unit> it = unitGraph.getHeads().iterator(); it.hasNext();) {
			//Added In
			//for (Unit headUnits:unitGraph.getHeads() )
			//{
			//	System.out.println("headUnit: " + headUnits.toString());
			//}
			//Added In
			Unit headUnit = (Unit) it.next();
			Block headBlock = unitToBlock.get(headUnit);
			if (headBlock.getHead() == headUnit) {
				mHeads.add(headBlock);
			} else {
				throw new RuntimeException("BlockGraph(): head Unit is not the first unit in the corresponding Block!");
			}
		}
		for (Iterator<Unit> it = unitGraph.getTails().iterator(); it.hasNext();) {
			Unit tailUnit = (Unit) it.next();
			Block tailBlock = unitToBlock.get(tailUnit);
			//Added in
			 //System.out.println("tailUnit : "+tailUnit.toString());
			 //System.out.println("tailBlock : "+tailBlock.getTail().toString());
			//Added in
			if (tailBlock.getTail() == tailUnit) {
				mTails.add(tailBlock);
			} else {
				throw new RuntimeException("BlockGraph(): tail Unit is not the last unit in the corresponding Block!");
			}
		}*/
		
		//addedin - add the nop units to the mtails
		int nop=0;
		for (Unit eachunit:unitGraph.getBody().getUnits()) 
		{
			Block tailBlock1;
			if (unitGraph.getHeads().contains(eachunit))
				mHeads.add(unitToBlock.get(eachunit));
			if (unitGraph.getTails().contains(eachunit))
				mTails.add(unitToBlock.get(eachunit));
			if (eachunit.toString().equals("nop"))
			{
				mTails.add(unitToBlock.get(eachunit));
				nop=1;
			}
			if(nop==1)
			{
				mHeads.add(unitToBlock.get(eachunit));
				nop=0;
			}
		}
		
		for (Unit eachUnit:mBody.getUnits())
		{
			 if(eachUnit.getTags().size()>0)
			 {
				 Tag tagVal2 = eachUnit.getTags().get(eachUnit.getTags().size()-1);
				 if(tagVal2.toString().equals("successor"))
				 {
					 System.out.println("13.successor found : "+eachUnit.toString());
					 System.out.println("13.successor tags : "+eachUnit.getTags().toString());
				 }
			 }
		 }
		//addedin
		//***make sure the tails have the right successor***
		ArrayList graphUnit = new ArrayList();
		Block successorBlk = null;
		Block tailBlk = null;
		Unit successorUnit = null;
		List<Block> succBlocks1 = new ArrayList<Block>();
		List<Unit> succUnits1 = new ArrayList<Unit>();
		PatchingChain<Unit> unitsInDummyMdt = unitGraph.getBody().getUnits();
		//find the successorblock
		
		for (Unit eachUnit:mBody.getUnits())
		{
			 if(eachUnit.getTags().size()>0)
			 {
				 Tag tagVal2 = eachUnit.getTags().get(eachUnit.getTags().size()-1);
				 if(tagVal2.toString().equals("successor"))
				 {
					 System.out.println("14.successor found : "+eachUnit.toString());
					 System.out.println("14.successor tags : "+eachUnit.getTags().toString());
				 }
			 }
		 }
		
		//for (Unit unitInChain:mUnits)
		for (Unit unitInChain:mBody.getUnits())
		{
			//System.out.println("tag of this unit : "+unitInChain.getTags());  
			//find which tag is contained in the unit
			int noOfTags=0;
			//check if the unit has any tag
			if(unitInChain.getTags().size()>0)
			{	
				    //get the last tag
					Tag lastTag = unitInChain.getTags().get(unitInChain.getTags().size()-1);
					System.out.println("finding successors : "+unitInChain.getTags()); 
					System.out.println("last successors : "+lastTag.toString()); 
					//if(unitInChain.getTags().toString().contains("successor"))
					if(lastTag.toString().equals("successor"))
					{
						//System.out.println("successor unit : "+unitInChain.toString());
						successorBlk = unitToBlock.get(unitInChain);
						successorUnit = unitInChain;
						//if(successorBlk!=null)
						succBlocks1.add(successorBlk);
						System.out.println("unitInChain : "+unitInChain.toString()); 
						if (successorBlk == null)
						{
							System.out.println("successor block is null...");
							//Stmt nop1=Jimple.v().new;
						}
						System.out.println("successorBlk : "+successorBlk.toString()); //successor block is null
						System.out.println("successor found : "+succBlocks1); 
					}
				//}
				else
				{
					//System.out.println("Number of tags is more than one.../n");  
				}
			}
			//find which tag is contained in the unit
		}
		
		for (Unit eachUnit:mBody.getUnits())
		{
			 if(eachUnit.getTags().size()>0)
			 {
				 Tag tagVal2 = eachUnit.getTags().get(eachUnit.getTags().size()-1);
				 if(tagVal2.toString().equals("successor"))
				 {
					 System.out.println("15.successor found : "+eachUnit.toString());
					 System.out.println("15.successor tags : "+eachUnit.getTags().toString());
				 }
			 }
		 }
		//find all the tailblock
		for (Unit unitInChain:mUnits)
		{
			//System.out.println("tag of this unit : "+unitInChain.getTags());  
			//find which tag is contained in the unit
			int noOfTags=0;
			//check if the unit has any tag
			if(unitInChain.getTags().size()>0)
			{	
				Tag lastTag = unitInChain.getTags().get(unitInChain.getTags().size()-1);
				if(lastTag.toString().equals("tail"))
				{
				    
					System.out.println("tail unit*** : "+unitInChain.getTags().toString()); 
					System.out.println("tail unit*** : "+unitInChain.toString()); 
					tailBlk = unitToBlock.get(unitInChain);
					//check if each tail unit has the right successor
					//if (successorBlk!=null)
					if (succBlocks1.size()>0)
					{
						//System.out.println("tail unit : "+unitInChain.toString());
						tailToSuccsMap.put(unitInChain,succBlocks1);
						tailBlk.setSuccs(Collections.unmodifiableList(succBlocks1));
						System.out.println("1.setSuccs...tailBlk : "+tailBlk.toString());
						System.out.println("successorBlk : "+successorBlk.toString());  
						System.out.println("succBlocks1 : "+succBlocks1.toString());
						System.out.println("block succ info : "+tailBlk.toString());
						succ_added=1;
					}
					else
						System.out.println("There is no successor for this tail!!!" +tailBlk.toString());
						
				}
				//}
				else
				{
					//System.out.println("Number of tags is more than one.../n");  
				}
			}
			//find which tag is contained in the unit
		}
		//***make sure the tails have the right successor***
		
		for (Iterator<Block> blockIt = blockList.iterator(); blockIt.hasNext();) {
			succ_added=0;
			Block block = blockIt.next();
			if(blockList.size()==71 && block.toString().contains("Block 4:"))
				System.out.println("forloop..."+ block.toString());
			//get the tag of the tail unit of the block
			Unit blkTailUnit = block.getTail();
			Tag blkTailTag=null;
			if(block.getTail().getTags().size()>0)
			{
			    blkTailTag = block.getTail().getTags().get(block.getTail().getTags().size()-1);
			    System.out.println("blkTailUnit tag : "+blkTailTag.toString());
			}
			//get the tag of the tail unit of the block
			List<Unit> predUnits = unitGraph.getPredsOf(block.getHead());
			List<Block> predBlocks = new ArrayList<Block>(predUnits.size());
			for (Iterator<Unit> predIt = predUnits.iterator(); predIt.hasNext();) {
				Unit predUnit = predIt.next();
				Block predBlock = unitToBlock.get(predUnit);
				//original
				/*if (predBlock == null) {
					throw new RuntimeException("BlockGraph(): block head mapped to null block!");
				}
				predBlocks.add(predBlock);*/
				//original
				//added in
				if (predBlock == null) {
					//throw new RuntimeException("BlockGraph(): block head mapped to null block!");
				}
				else
				{
					//check if the predBlk's tail has the same tag
					Unit predBlkTailUnit = predBlock.getTail();
					Tag predBlkTailTag=null;
					if(predBlock.getTail().getTags().size()>0)
					{
						predBlkTailTag =  (StringTag) predBlock.getTail().getTags().get(predBlock.getTail().getTags().size()-1);
						//System.out.println("pred block tail tag : "+predBlkTailTag.toString());
						if (blkTailTag != null && predBlkTailTag != null)
						//if (blkTailUnit.getTags() != null && predBlock.getTail().getTags() != null)
						{
							String blkTailTagStr = blkTailTag.toString();
							//String blkTailTagStr = blkTailUnit.getTags().toString();
							String predBlkTailTagStr = predBlkTailTag.toString();
							//String predBlkTailTagStr = predBlock.getTail().getTags().toString();
							if (predBlkTailTagStr.equals(blkTailTagStr))
							{
								//System.out.println("pred block has same tail tag: ");
								//System.out.println("block tail tag: "+blkTailTag);
								//System.out.println("pred block tail tag: "+predBlkTailTag );
							}
							else
								predBlocks.add(predBlock);
						}
						else
							predBlocks.add(predBlock);
						
					}
					//check if the predBlk's tail has the same tag
					else
						predBlocks.add(predBlock); //original line
				}
				
				//added in
			}

			if (predBlocks.size() == 0) {
				block.setPreds(Collections.<Block> emptyList());
				
	

				// If the UnreachableCodeEliminator is not eliminating
				// unreachable handlers, then they will have no
				// predecessors, yet not be heads.
				/*
				 * if (! mHeads.contains(block)) { throw new
				 * RuntimeException("Block with no predecessors is not a head!"
				 * );
				 * 
				 * // Note that a block can be a head even if it has //
				 * predecessors: a handler that might catch an exception //
				 * thrown by the first Unit in the method. }
				 */
			} else {
				block.setPreds(Collections.unmodifiableList(predBlocks));
				if (block.getHead() == mUnits.getFirst()) {
					mHeads.add(block); // Make the first block a head
					// even if the Body is one huge loop.
				}
			}
			
			//Added in to correct the successor units for the tails
			List<Unit> succUnits = unitGraph.getSuccsOf(block.getTail());
			List<Block> succBlocks = new ArrayList<Block>(succUnits.size());
			/*
			StringTag tagVal = null;
			if(block.getTail().getTags().size()>0)
			{	
				tagVal =  (StringTag) block.getTail().getTags().get(0);
				if(tagVal.toString() =="tail")
				{
					List<Unit> succUnits1 = new ArrayList();
					if(successorUnit!=null)
					{	succUnits1.add(successorUnit);
						unitGraph.setSuccsOf(block.getTail(),succUnits1);
				        succUnits = unitGraph.getSuccsOf(block.getTail());
				        System.out.println("prevUnit : "+unitGraph.getPredsOf(block.getTail()));
				        System.out.println("tailUnit : "+block.getTail().toString());
						System.out.println("succUnits**** : "+succUnits.toString());
						succBlocks = new ArrayList<Block>(succUnits.size());
						for (Iterator<Unit> succIt = succUnits.iterator(); succIt.hasNext();) {
							Unit succUnit = succIt.next();
							Block succBlock = unitToBlock.get(succUnit);
							if (succBlock == null) {
								//throw new RuntimeException("BlockGraph(): block tail mapped to null block!");
							}
							else
								succBlocks.add(succBlock);
						}
						
						Map<Unit,List<Unit>> succMap = unitGraph.getSuccMap();
						for (Map.Entry entry : succMap.entrySet()) 
						{
							System.out.println("Key : " +entry.getKey() );
						    System.out.println("Value : "+entry.getValue());
						}
						System.out.println("Map tail ended*************************************************");
					}
				}
			}
			
			//Added in to correct the successor units for the tails
			else { //else was added after if*/
			succUnits = unitGraph.getSuccsOf(block.getTail());
			System.out.println("succUnits : "+succUnits.toString());
			succBlocks = new ArrayList<Block>(succUnits.size());
			for (Iterator<Unit> succIt = succUnits.iterator(); succIt.hasNext();) {
				Unit succUnit = succIt.next();
				//System.out.println("succUnit :"+succUnit);
				Block succBlock = unitToBlock.get(succUnit);
				//Added In
				
				//System.out.println("succUnit : "+succUnit.toString());
				//Added In
				//original
				/*if (succBlock == null) {
					throw new RuntimeException("BlockGraph(): block tail mapped to null block!");
				}
				succBlocks.add(succBlock);*/
				//original
				//***edited***
				if (succBlock == null) {
					//throw new RuntimeException("BlockGraph(): block tail mapped to null block!");
				}
				else
					succBlocks.add(succBlock);
				
				/*Map<Unit,List<Unit>> succMap = unitGraph.getSuccMap();
				for (Map.Entry entry : succMap.entrySet()) 
				{
					System.out.println("Key : " +entry.getKey() );
				    System.out.println("Value : "+entry.getValue());
				}
				System.out.println("Map ended...******************************************************************************************************************");*/
				//***edited***
			}
			//}
			
			
			
			
			if (succBlocks.size() == 0) {
				block.setSuccs(Collections.<Block> emptyList());
				System.out.println("2.setSuccs");
				System.out.println("block succ info : "+block.toString());
				succ_added=1;
				if (!mTails.contains(block)) {
					// if this block is totally empty and unreachable, we remove it
					if (block.getPreds().isEmpty()
							&& block.getHead() == block.getTail()
							&& block.getHead() instanceof NopStmt)
						blockIt.remove();
					//added in line 365 and 366 was originally there...commented out
					//else
						//throw new RuntimeException("Block with no successors is not a tail!: " + block.toString());
					// Note that a block can be a tail even if it has
					// successors: a return that throws a caught exception.
				}
			} else 
			{
				//Added in - if the block's tail has the tail tag, the continue
				if(block.getTail().getTags().size()>0)
				{
					//StringTag tagVal1 =  (StringTag) block.getTail().getTags().get(0);
					Tag tagVal1 =   block.getTail().getTags().get(block.getTail().getTags().size()-1);
					
					/*if(tagVal1.toString() =="oldtail")
					{
						System.out.println("oldtail *** "+block.getTail().toString() );
						if(tailToSuccsMap.containsKey(block.getTail()))
							System.out.println("contains key...\n");
						else
							System.out.println("does not contains key...\n");
						//List <Block> succBlkList = tailToSuccsMap.get(block.getTail());
						//System.out.println("succBlkList : "+succBlkList.toString() );
						//tailToSuccsMap.get(block.getTail());
						//System.out.println("list size:"+succBlkList.size());
						//block.setSuccs(Collections.unmodifiableList(succBlkList));
						continue;
					}*/
					
					//if(tagVal1.toString().contains("oldtail"))
					//if(block.getTail().getTags().toString().contains("oldtail"))
					if(tagVal1.toString().contains("oldtail"))
					{
						//get the number of the tail
						String[] parts = tagVal1.toString().split("_");
						//find the unit which is the successor of this with oldsuccessor_number
						String succUnitTag = "oldsuccessor_" + parts[1];
						System.out.println("succUnitTag : "+succUnitTag.toString());
						for (Unit unitInChain:mUnits)
						{
							if(unitInChain.getTags().size()>0)
							{
								//StringTag tagVal2 =  (StringTag) unitInChain.getTags().get(0);
								//if(tagVal2.toString().equals(succUnitTag))
								//if(unitInChain.getTags().get(0).toString().equals(succUnitTag))
								Tag unitInChainTag = unitInChain.getTags().get(unitInChain.getTags().size()-1);
								System.out.println("unitInChainTag : "+unitInChainTag.toString());
								//if(unitInChain.getTags().toString().contains(succUnitTag))
								//if(unitInChainTag.toString().contains(succUnitTag))
								if(unitInChainTag.toString().equals(succUnitTag))
								{
									List<Block> succBlocks2 = new ArrayList<Block>();
									//System.out.println("tail found : "+block.getTail());
									//System.out.println("successor found : "+unitInChain.toString());
									successorBlk = unitToBlock.get(unitInChain);
									//successorUnit = unitInChain;
									//succBlocks1.clear();
									succBlocks2.add(successorBlk);
									//succBlocks1.add(successorBlk);
									block.setSuccs(Collections.unmodifiableList(succBlocks2)); //changed 1 ->2
									System.out.println("3.setSuccs");
									System.out.println("block succ info : "+block.toString());
									succ_added=1;
								}
								//else
									//continue;
							}
						}
						//continue;
					}
					//if(block.getTail().getTags().size()>0)
						//System.out.println("*****tags***** : "+block.getTail().getTags());
					//if(tagVal1.toString() =="tail")
					Tag blockTag = block.getTail().getTags().get(block.getTail().getTags().size()-1);
					//if(block.getTail().getTags().toString().contains("tail"))
					if(blockTag.toString().contains("tail"))
					{
						//System.out.println("continued..."
						System.out.println("succBlocks "+succBlocks.toString());
						System.out.println("block succ info : "+block.toString());
						if(block.getSuccs()==null)
						{
							
							//block.setSuccs(Collections.unmodifiableList(succBlocks));
							System.out.println("no successor blocks... "+succBlocks.toString());
						}
						continue;
					}
				}
				//block.setSuccs(Collections.unmodifiableList(succBlocks)); //originally here
				//Added in - if the block's tail has the tail tag, the continue
				
				//StringTag tagVal1 = null;
				Tag tagVal1 = null;
				//System.out.println("!!!!!");
				//System.out.println("block printed: "+block.toString());
				if(block.getTail().getTags().size()>0)
				{
					//tagVal1 =  (StringTag) block.getTail().getTags().get(0);
					tagVal1 =   block.getTail().getTags().get(block.getTail().getTags().size()-1);
					//if(!tagVal1.toString().contains("tail"))
					//if(!block.getTail().getTags().toString().contains("tail"))
					if(!tagVal1.toString().contains("tail"))
					{
						//System.out.println("not contain tail");
						block.setSuccs(Collections.unmodifiableList(succBlocks));
						System.out.println("4.setSuccs");
						System.out.println("block printed: "+block.toString());
						succ_added=1;
					}
					else
						System.out.println("contain tail ");
				}
				else
				{
					//System.out.println("else condition ... tail");
					block.setSuccs(Collections.unmodifiableList(succBlocks));
					System.out.println("5.setSuccs");
					System.out.println("block printed: "+block.toString());
					succ_added=1;
				}
				/*for (Block blockInList:blockList)
				{
					System.out.println("block from list b4 !!!!!"+blockInList);
				}
				System.out.println("!!!!!\n");*/
			}
			
			if(block.getSuccs().size()==0)
			{
				System.out.println("Succ has not been added..."+ block.toString());
				System.out.println("succBlocks..."+ succBlocks.toString());
			}
		}//end of for loop
		//Added in
		//checking the blocklist
		//for (Block blockInList:blockList)
		//	System.out.println("block from list : "+blockInList);
		//Added in
		mBlocks = Collections.unmodifiableList(blockList);
		mHeads = Collections.unmodifiableList(mHeads);
		if (mTails.size() == 0) {
			mTails = Collections.emptyList();
		} else {
			mTails = Collections.unmodifiableList(mTails);
		}
		return unitToBlock;
	}

	/**
	 * A utility method which creates a new block and adds information about it
	 * to data structures used to build the graph.
	 *
	 * @param head
	 *            The first unit in the block.
	 * @param tail
	 *            The last unit in the block.
	 * @param index
	 *            The index of this block this {@link Body}.
	 * @param length
	 *            The number of units in this block.
	 * @param blockList
	 *            The list of blocks for this method. <code>addBlock()</code>
	 *            will add the newly created block to this list.
	 * @param unitToBlock
	 *            A map from units to blocks. <code>addBlock()</code> will add
	 *            mappings from <code>head</code> and <code>tail</code> to the
	 *            new block
	 */
	private int addBlock(Unit head, Unit tail, int index, int length, List<Block> blockList,
			Map<Unit, Block> unitToBlock) {
		Block block = new Block(head, tail, mBody, index, length, this);
		for (Block inBlkList:blockList)
	    {
			//original
			String blockStr = block.toString().substring(10);
			//System.out.println("blockStr1 : "+blockStr);
			//System.out.println("block tail1 : "+tail.toString());
			String inBlkListStr = inBlkList.toString().substring(10);
			//System.out.println("blockStr2 : "+inBlkListStr);
			//System.out.println("block tail2 : "+inBlkList.getTail().toString());
			
			//new mdt
			/*
			String blockStr = "";
			String inBlkListStr = "";
			try
			{
				blockStr = block.toString().substring(10);
			}
			catch (Exception e){
				continue;
			}
			
			try
			{
				inBlkListStr = inBlkList.toString().substring(10);
			}
			catch (Exception e){
				continue;
			}*/
			
			
	        /*if(blockStr.toString().equals(inBlkListStr))
			{
	        	System.out.println("DUPLICATE BLOCK");
	        	System.out.println("blockStr :"+blockStr);
	        	System.out.println("inBlkListStr :"+inBlkListStr);
	        	
	        	
		        return 0;
		     }*/
			
			//if(blockStr.toString().equals(inBlkListStr))
			if(blockList.contains(block))
			{
	        	System.out.println("DUPLICATE BLOCK");
	        	System.out.println("blockStr :"+blockStr);
	        	System.out.println("inBlkListStr :"+inBlkListStr);
		        return 0;
		    }
			
	    }
		
		blockList.add(block);
		unitToBlock.put(tail, block);
		unitToBlock.put(head, block);
		System.out.println("addBlock block : "+block);
		System.out.println("tail : "+tail.toString());
		System.out.println("tail tags : "+tail.getTags());
		System.out.println("head : "+head.toString());
		System.out.println("head tags: "+head.getTags());
		
		return 1;
	}

	/**
	 * Returns the {@link Body} this {@link BlockGraph} is derived from.
	 * 
	 * @return The {@link Body} this {@link BlockGraph} is derived from.
	 */
	public Body getBody() {
		return mBody;
	}

	/**
	 * Returns a list of the Blocks composing this graph.
	 * 
	 * @return A list of the blocks composing this graph in the same order as
	 *         they partition underlying Body instance's unit chain.
	 * @see Block
	 */
	public List<Block> getBlocks() {
		return mBlocks;
	}
	//added in
	public List<Block> setBlocks (List<Block> a)
	{
		List<Block> mBlocksNew = new ArrayList();
		//replace mBlocks
		mBlocks.clear();
		for (Block eachOne:a)
		{
			mBlocks.add(eachOne);
		}
		return mBlocksNew;
	}
	//added in
	public List<Block> addBlocks (Block a)
	{
		//List<Block> mBlocksNew = new ArrayList();
		mBlocks.add(a);
		return mBlocks;
	}
	public String toString() {

		Iterator<Block> it = mBlocks.iterator();
		StringBuffer buf = new StringBuffer();
		while (it.hasNext()) {
			Block someBlock = it.next();

			buf.append(someBlock.toString() + '\n');
		}

		return buf.toString();
	}

	/* DirectedGraph implementation */
	public List<Block> getHeads() {
		return mHeads;
	}

	public List<Block> getTails() {
		return mTails;
	}

	public List<Block> getPredsOf(Block b) {
		return b.getPreds();
	}

	public List<Block> getSuccsOf(Block b) {
		return b.getSuccs();
	}

	public int size() {
		return mBlocks.size();
	}

	public Iterator<Block> iterator() {
		return mBlocks.iterator();
	}
}