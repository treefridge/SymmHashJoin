/*-------------------------------------------------------------------------
 *
 * nodeHashjoin.c
 *	  Routines to handle hash join nodes
 *
 * Portions Copyright (c) 1996-2005, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  $PostgreSQL: pgsql/src/backend/executor/nodeHashjoin.c,v 1.75.2.3 2005/11/28 23:46:24 tgl Exp $
 *
 *-------------------------------------------------------------------------
 */

#include "postgres.h"

#include "executor/executor.h"
#include "executor/hashjoin.h"
#include "executor/nodeHash.h"
#include "executor/nodeHashjoin.h"
#include "optimizer/clauses.h"
#include "utils/memutils.h"


static TupleTableSlot *ExecHashJoinOuterGetTuple(PlanState *outerNode,
                                                 HashJoinState *hjstate,
                                                 uint32 *hashvalue);
static TupleTableSlot *ExecHashJoinGetSavedTuple(HashJoinState *hjstate,
                                                 BufFile *file,
                                                 uint32 *hashvalue,
                                                 TupleTableSlot *tupleSlot);
static int	ExecHashJoinNewBatch(HashJoinState *hjstate);


/* ----------------------------------------------------------------
 *		ExecHashJoin
 *
 *		This function implements the Hybrid Hashjoin algorithm.
 *
 *		Note: the relation we build hash table on is the "inner"
 *			  the other one is "outer".
 * ----------------------------------------------------------------
 */
TupleTableSlot *				/* return: a tuple or NULL */
ExecHashJoin(HashJoinState *node)
{
    EState	   *estate;
    HashState  *inner_hashNode;//CSI3130
    HashState  *outer_hashNode;//CSI3130
    List	   *joinqual;
    List	   *otherqual;
    TupleTableSlot *inntuple;
    TupleTableSlot *outtuple;
    ExprContext *econtext;
    ExprDoneCond isDone;
    HashJoinTable inner_hashtable;//CSI3130
    HashJoinTable outer_hashtable;//CSI3130
    HeapTuple	curtuple;
    TupleTableSlot *outerTupleSlot;
    TupleTableSlot *innerTupleSlot;//CSI3130
    uint32		hashvalue;
    int		batchno;

    /*
     * get information from HashJoin node
     */
    estate = node->js.ps.state;
    joinqual = node->js.joinqual;
    otherqual = node->js.ps.qual;
    inner_hashNode = (HashState *) innerPlanState(node);
    outer_hashNode = (HashState *) outerPlanState(node);

    /*
     * get information from HashJoin state
     */
    inner_hashtable = node->hj_InnerHashTable;//CSI3130
    outer_hashtable = node->hj_OuterHashTable;//CSI3130
    econtext = node->js.ps.ps_ExprContext;

    /*
     * Check to see if we're still projecting out tuples from a previous join
     * tuple (because there is a function-returning-set in the projection
     * expressions).  If so, try to project another one.
     */

elog(17,  "HI");
    /*
     * If we're doing an IN join, we want to return at most one row per outer
     * tuple; so we can stop scanning the inner scan if we matched on the
     * previous try.
     */
    if (node->js.jointype == JOIN_IN && node->hj_MatchedOuter)
            node->hj_NeedNewOuter = true;

    /*
     * Reset per-tuple memory context to free any expression evaluation
     * storage allocated in the previous tuple cycle.  Note this can't happen
     * until we're done projecting out tuples from a join tuple.
     */
    ResetExprContext(econtext);

    /*
     * if this is the first call, build the hash table for inner relation
     */
    if (inner_hashtable == NULL && outer_hashtable == NULL)
    {
            /*
             * If the outer relation is completely empty, we can quit without
             * building the hash table.  However, for an inner join it is only a
             * win to check this when the outer relation's startup cost is less
             * than the projected cost of building the hash table.	Otherwise it's
             * best to build the hash table first and see if the inner relation is
             * empty.  (When it's an outer join, we should always make this check,
             * since we aren't going to be able to skip the join on the strength
             * of an empty inner relation anyway.)
             *
             * If we are rescanning the join, we make use of information gained
             * on the previous scan: don't bother to try the prefetch if the
             * previous scan found the outer relation nonempty.  This is not
             * 100% reliable since with new parameters the outer relation might
             * yield different results, but it's a good heuristic.
             *
             * The only way to make the check is to try to fetch a tuple from the
             * outer plan node.  If we succeed, we have to stash it away for later
             * consumption by ExecHashJoinOuterGetTuple.
             */

            /*
             * create the hash table
             */
            //CSI3130-->
            inner_hashtable = ExecHashTableCreate((Hash *) inner_hashNode->ps.plan,
                                                   node->hj_HashOperators);
            node->hj_InnerHashTable = inner_hashtable;
            outer_hashtable = ExecHashTableCreate((Hash *) outer_hashNode->ps.plan,
                                                   node->hj_HashOperators);
            node->hj_OuterHashTable = outer_hashtable;
            //CSI3130<--

            /*
             * execute the Hash node, to build the hash table
             */
            inner_hashNode->hashtable = inner_hashtable;//CSI3130
            outer_hashNode->hashtable = outer_hashtable;//CSI3130
    }
    elog(17,"function ExecHashJoin: process started");
    /*
     * run the hash join process
     */
    for (;;)
    {
        /*
         * If we don't have an outer tuple, get the next one//CSI3130-->
         */
        if ((node->hj_NeedNewInner || node->inner_exhausted) && (node->hj_NeedNewOuter || node->outer_exhausted))
        {
            if(node->isNextFetchInner)
            {
                if(!node->inner_exhausted){
                    innerTupleSlot = ExecProcNode((PlanState*) inner_hashNode);
                    if(node->outer_exhausted)
                    {
                        node->isNextFetchInner = true;
                    }
                    else
                    {
                        node->isNextFetchInner = false; // deal with later!!!
                    }
                    node->js.ps.ps_InnerTupleSlot = innerTupleSlot;

                    if(!TupIsNull(innerTupleSlot)){
                        node->hj_NeedNewInner = false;
                        //bool isNullAttr;
                        elog(17,  "got new inner \n");
                    }

                    //Get Hash Value
                    ExprContext *econtext = node->js.ps.ps_ExprContext;
                    econtext->ecxt_innertuple = innerTupleSlot;
                    hashvalue = ExecHashGetHashValue(outer_hashtable, econtext,
                                                     node->hj_InnerHashKeys);
                    node->js.ps.ps_InnerTupleSlot = innerTupleSlot;
                    econtext->ecxt_innertuple = node->js.ps.ps_InnerTupleSlot;

                    node->hj_InnerCurHashValue = hashvalue;
                    ExecHashGetBucketAndBatch(outer_hashtable, hashvalue, &node->hj_OuterCurBucketNo, &batchno);
                    node->hj_OuterCurTuple = NULL; //Reset current tuple in bucket in outer hash table
                } else {
                    node->inner_exhausted = true;
                }
            }
            else
            {
                //outer
                if(!node->outer_exhausted){
                    if(outer_hashNode == NULL)
                    {
                        elog(17, "IT IS NUUUUUUL \n");
                    }
                    outerTupleSlot = ExecProcNode((PlanState*) outer_hashNode);
                    if(node->inner_exhausted)
                    {
                        node->isNextFetchInner = false;
                    } else {
                        node->isNextFetchInner = true; // deal with later!!!
                    }
                    node->js.ps.ps_OuterTupleSlot = outerTupleSlot;

                    if(!TupIsNull(outerTupleSlot)){
                        node->hj_NeedNewOuter = false;
                        //bool isNullAttr;
                        elog(17,  "got new outer \n");
                    }

                    //Get Hash Value
                    ExprContext *econtext = node->js.ps.ps_ExprContext;
                    econtext->ecxt_outertuple = outerTupleSlot;
                    hashvalue = ExecHashGetHashValue(inner_hashtable, econtext,
                                                        node->hj_OuterHashKeys);
                    node->js.ps.ps_OuterTupleSlot = outerTupleSlot;
                    econtext->ecxt_outertuple = node->js.ps.ps_OuterTupleSlot;

                    node->hj_OuterCurHashValue = hashvalue;
                    ExecHashGetBucketAndBatch(inner_hashtable, hashvalue, &node->hj_InnerCurBucketNo, &batchno);
                    node->hj_InnerCurTuple = NULL; //Reset current tuple in bucket in outer hash table
                } else {
                    node->outer_exhausted = true;
                    elog(17, "outer exhausted \n");
                }
            }
            //end outer
        }

        if (node->inner_exhausted && node->outer_exhausted)
        {
            /* end of join */
            elog(17,"In function ExecHashJoin: both inner and outer are exhausted!");
            elog(17,  "both inner (%f tuples) and outer (%f tuples) exhausted\n", inner_hashtable->totalTuples, outer_hashtable->totalTuples);
            elog(17,  "Got %d matches by probing inner hash table\n", node->matches_by_probing_inner);
            elog(17,  "Got %d matches by probing outer hash table\n", node->matches_by_probing_outer);
            elog(17,  "Assuming outer is always probed first\n");
            return NULL;
        }

        //CSI3130<--
        /*
         * OK, scan the selected hash bucket for matches
         */
        if(!TupIsNull(node->js.ps.ps_InnerTupleSlot) && node->isNextFetchInner){//CSI3130-->
            elog(17,"In function ExecHashJoin: probing for matches to the inner tuple");
            for (;;)
            {
                ExprContext *econtext = node->js.ps.ps_ExprContext;
                econtext->ecxt_innertuple = node->js.ps.ps_InnerTupleSlot;

                curtuple = ExecScanHashBucket_probingOuter(node, econtext);
                if (curtuple == NULL){
                    elog(17,"ExecHashJoin: no more matches for the current inner tuple");        
                    node->isNextFetchInner = false;
                    break;			/* out of matches */
                }
                /*
                 * we've got a match, but still need to test non-hashed quals
                 */
                elog(17,"ExecHashJoin: we've got a match, but still need to test non-hashed quals");
                outtuple = ExecStoreTuple(curtuple,
                                          node->hj_OuterHashTupleSlot,
                                          InvalidBuffer,
                                          false);	/* don't pfree this tuple */
                econtext->ecxt_outertuple = outtuple;

                /* reset temp memory each time to avoid leaks from qual expr */
                ResetExprContext(econtext);

                /*
                 * if we pass the qual, then save state for next call and have
                 * ExecProject form the projection, store it in the tuple table,
                 * and return the slot.
                 *
                 * Only the joinquals determine MatchedOuter status, but all quals
                 * must pass to actually return the tuple.
                 */
                if( !node->outer_exhausted
                   && !node->hj_NeedNewOuter
                   && !TupIsNull(node->js.ps.ps_OuterTupleSlot)
                   && ItemPointerGetBlockNumber(&curtuple->t_data->t_ctid) == ItemPointerGetBlockNumber(&node->js.ps.ps_OuterTupleSlot->tts_tuple->t_data->t_ctid)
                   && ItemPointerGetOffsetNumber(&curtuple->t_data->t_ctid) == ItemPointerGetOffsetNumber(&node->js.ps.ps_OuterTupleSlot->tts_tuple->t_data->t_ctid)){
                    //Do nothing? //CSI3130
                } else if (joinqual == NIL || ExecQual(joinqual, econtext, false))
                {

                    if (otherqual == NIL || ExecQual(otherqual, econtext, false))
                    {
                        TupleTableSlot *result;
                        result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);

                        if (isDone != ExprEndResult)
                        {
                            elog(WARNING,"ExecHashJoin: Found a match!");
                            node->matches_by_probing_outer++;//CSI3130
                            node->js.ps.ps_TupFromTlist =
                            (isDone == ExprMultipleResult);
                            return result;
                        }
                    }
                }
            }

            //Did not find a match for inner tuple, so we need another.
            node->hj_NeedNewInner = true;
            node->js.ps.ps_InnerTupleSlot = NULL;
            node->isNextFetchInner = false;//Let the outer have a turn
            elog(17,"ExecHashJoin: No inner tuple match found, set values, outer's turn next.");
            continue;//go directly to the next fetching.
        }
        /*
         * OK, scan the selected hash bucket for matches
         */
        if(!TupIsNull(node->js.ps.ps_OuterTupleSlot) && !node->isNextFetchInner){//CSI3130-->
            elog(17,"In function ExecHashJoin: probing for matches to the outer tuple");
            for (;;)
            {
                ExprContext *econtext = node->js.ps.ps_ExprContext;
                econtext->ecxt_outertuple = node->js.ps.ps_OuterTupleSlot;

                curtuple = ExecScanHashBucket_probingInner(node, econtext);
                if (curtuple == NULL){
                    elog(17,"ExecHashJoin: no more matches for the current outer tuple");        
                    node->isNextFetchInner = true;
                    break;			/* out of matches */
                }
                /*
                 * we've got a match, but still need to test non-hashed quals
                 */
                elog(17,"ExecHashJoin: we've got a match, but still need to test non-hashed quals");
                inntuple = ExecStoreTuple(curtuple,
                                          node->hj_InnerHashTupleSlot,
                                          InvalidBuffer,
                                          false);	/* don't pfree this tuple */
                econtext->ecxt_innertuple = inntuple;

                /* reset temp memory each time to avoid leaks from qual expr */
                ResetExprContext(econtext);

                /*
                 * if we pass the qual, then save state for next call and have
                 * ExecProject form the projection, store it in the tuple table,
                 * and return the slot.
                 *
                 * Only the joinquals determine MatchedOuter status, but all quals
                 * must pass to actually return the tuple.
                 */
                if (joinqual == NIL || ExecQual(joinqual, econtext, false))
                {
                    if (otherqual == NIL || ExecQual(otherqual, econtext, false))
                    {
                        TupleTableSlot *result;

                        result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);

                        if (isDone != ExprEndResult)
                        {
                            elog(WARNING,"ExecHashJoin: Found a match!");
                            node->matches_by_probing_inner++;
                            node->js.ps.ps_TupFromTlist = (isDone == ExprMultipleResult);
                            return result;
                        }
                    }

                    /*
                     * If we didn't return a tuple, may need to set NeedNewOuter
                     */
                    //Did not find a match for inner tuple, so we need another.
                    node->hj_NeedNewOuter = true;
                    node->js.ps.ps_OuterTupleSlot = NULL;
                    node->isNextFetchInner = true;//Let the outer have a turn
                    elog(17,"ExecHashJoin: No outer tuple match found, set values, outer's turn next.");
                    continue;//go directly to the next fetching.
                }
            }
        }//CSI3130<--

        /*
         * Now the current outer tuple has run out of matches, so check
         * whether to emit a dummy outer-join tuple. If not, loop around to
         * get a new outer tuple.
         */


        if (!node->hj_MatchedOuter &&
            node->js.jointype == JOIN_LEFT)
        {
            elog(17,"ExecHashJoin: join type left");
                        /*
             * We are doing an outer join and there were no join matches for
             * this outer tuple.  Generate a fake join tuple with nulls for
             * the inner tuple, and return it if it passes the non-join quals.
             */
            econtext->ecxt_innertuple = node->hj_NullInnerTupleSlot;

            if (ExecQual(otherqual, econtext, false))
            {
                /*
                 * qualification was satisfied so we project and return the
                 * slot containing the result tuple using ExecProject().
                 */
                TupleTableSlot *result;

                result = ExecProject(node->js.ps.ps_ProjInfo, &isDone);

                if (isDone != ExprEndResult)
                {
                    node->js.ps.ps_TupFromTlist =
                    (isDone == ExprMultipleResult);
                    return result;
                }
            }
        }
    }
}


/* ----------------------------------------------------------------
 *		ExecInitHashJoin
 *
 *		Init routine for HashJoin node.
 * ----------------------------------------------------------------
 */
HashJoinState *
ExecInitHashJoin(HashJoin *node, EState *estate)
{
	HashJoinState *hjstate;
	Hash	   *outerNode;
	Hash	   *innerNode;//*CSI3130*Project
	List	   *lclauses;
	List	   *rclauses;
	List	   *hoperators;
	ListCell   *l;
    
	/*
	 * create state structure
	 */
	hjstate = makeNode(HashJoinState);
	hjstate->js.ps.plan = (Plan *) node;
	hjstate->js.ps.state = estate;
    
	/*
	 * Miscellaneous initialization
	 *
	 * create expression context for node
	 */
	ExecAssignExprContext(estate, &hjstate->js.ps);
    
	/*
	 * initialize child expressions
	 */
	hjstate->js.ps.targetlist = (List *)
    ExecInitExpr((Expr *) node->join.plan.targetlist,
                 (PlanState *) hjstate);
	hjstate->js.ps.qual = (List *)
    ExecInitExpr((Expr *) node->join.plan.qual,
                 (PlanState *) hjstate);
	hjstate->js.jointype = node->join.jointype;
	hjstate->js.joinqual = (List *)
    ExecInitExpr((Expr *) node->join.joinqual,
                 (PlanState *) hjstate);
	hjstate->hashclauses = (List *)
    ExecInitExpr((Expr *) node->hashclauses,
                 (PlanState *) hjstate);
    
	/*
	 * initialize child nodes
	 */
	outerNode = (Hash *) outerPlan(node);
	innerNode = (Hash *) innerPlan(node);//CSI3130*Project
    
	outerPlanState(hjstate) = ExecInitNode(outerNode, estate);
	innerPlanState(hjstate) = ExecInitNode((Plan *) innerNode, estate);//CSI3130*Project
    
#define HASHJOIN_NSLOTS 3
    
	/*
	 * tuple table initialization
	 */
	ExecInitResultTupleSlot(estate, &hjstate->js.ps);
	hjstate->hj_OuterTupleSlot = ExecInitExtraTupleSlot(estate);
	hjstate->hj_InnerTupleSlot = ExecInitExtraTupleSlot(estate);
    
	switch (node->join.jointype)
	{
		case JOIN_INNER:
		case JOIN_IN:
			break;
		case JOIN_LEFT:
			hjstate->hj_NullInnerTupleSlot =
            ExecInitNullTupleSlot(estate,
                                  ExecGetResultType(innerPlanState(hjstate)));
			break;
		default:
			elog(ERROR, "unrecognized join type: %d",
				 (int) node->join.jointype);
	}
    
	/*
	 * now for some voodoo.  our temporary tuple slot is actually the result
	 * tuple slot of the Hash node (which is our inner plan).  we do this
	 * because Hash nodes don't return tuples via ExecProcNode() -- instead
	 * the hash join node uses ExecScanHashBucket() to get at the contents of
	 * the hash table.	-cim 6/9/91
	 */
	{
		HashState  *hashstate = (HashState *) innerPlanState(hjstate);
		TupleTableSlot *slot = hashstate->ps.ps_ResultTupleSlot;
        
		hjstate->hj_InnerTupleSlot = slot;
        //CSI3130-->
		HashState *outerhashstate = (HashState *) outerPlanState(hjstate);
		slot = outerhashstate->ps.ps_ResultTupleSlot;
        
		hjstate->hj_OuterTupleSlot = slot;
        //CSI3130<--
	}
    
	/*
	 * initialize tuple type and projection info
	 */
	ExecAssignResultTypeFromTL(&hjstate->js.ps);
	ExecAssignProjectionInfo(&hjstate->js.ps);
    
	ExecSetSlotDescriptor(hjstate->hj_OuterTupleSlot,
						  ExecGetResultType(outerPlanState(hjstate)),
						  false);
    //CSI3130-->
	ExecSetSlotDescriptor(hjstate->hj_InnerTupleSlot,
						  ExecGetResultType(innerPlanState(hjstate)),
						  false);
    //CSI3130<--
	/*
	 * initialize hash-specific info
	 */
	hjstate->hj_OuterHashTable = NULL;
	hjstate->hj_InnerHashTable = NULL;
	hjstate->hj_FirstOuterTupleSlot = NULL;
	hjstate->hj_FirstInnerTupleSlot = NULL;//CSI3130
    
    //CSI3130-->
	hjstate->hj_InnerCurHashValue = 0;
	hjstate->hj_InnerCurBucketNo = 0;
	hjstate->hj_InnerCurTuple = NULL;
        hjstate->hj_OuterCurHashValue = 0;
	hjstate->hj_OuterCurBucketNo = 0;
	hjstate->hj_OuterCurTuple = NULL;
    
        bool        inner_exhausted = false;
        bool        outer_exhausted = false;
    //CSI3130<--
    
	/*
	 * Deconstruct the hash clauses into outer and inner argument values, so
	 * that we can evaluate those subexpressions separately.  Also make a list
	 * of the hash operator OIDs, in preparation for looking up the hash
	 * functions to use.
	 */
	lclauses = NIL;
	rclauses = NIL;
	hoperators = NIL;
	foreach(l, hjstate->hashclauses)
	{
		FuncExprState *fstate = (FuncExprState *) lfirst(l);
		OpExpr	   *hclause;
        
		Assert(IsA(fstate, FuncExprState));
		hclause = (OpExpr *) fstate->xprstate.expr;
		Assert(IsA(hclause, OpExpr));
		lclauses = lappend(lclauses, linitial(fstate->args));
		rclauses = lappend(rclauses, lsecond(fstate->args));
		hoperators = lappend_oid(hoperators, hclause->opno);
	}
	hjstate->hj_OuterHashKeys = lclauses;
	hjstate->hj_InnerHashKeys = rclauses;
	hjstate->hj_HashOperators = hoperators;
	/* child Hash node needs to evaluate inner hash keys, too */
	((HashState *) innerPlanState(hjstate))->hashkeys = rclauses;
	((HashState *) outerPlanState(hjstate))->hashkeys = lclauses;//CSI3130
    
	hjstate->js.ps.ps_OuterTupleSlot = NULL;
        hjstate->js.ps.ps_InnerTupleSlot = NULL;//CSI3130
	hjstate->js.ps.ps_TupFromTlist = false;
	hjstate->hj_NeedNewInner = true;//CSI3130
	hjstate->hj_NeedNewOuter = true;
	hjstate->hj_MatchedOuter = false;
	//hjstate->hj_OuterNotEmpty = false;//CSI3130
    
    //CSI3130-->
        int         matches_by_probing_inner = 0;
        int         matches_by_probing_outer = 0;
    //<--CSI3130
    
	return hjstate;
}

int
ExecCountSlotsHashJoin(HashJoin *node)
{
	return ExecCountSlotsNode(outerPlan(node)) +
    ExecCountSlotsNode(innerPlan(node)) +
    HASHJOIN_NSLOTS;
}

/* ----------------------------------------------------------------
 *		ExecEndHashJoin
 *
 *		clean up routine for HashJoin node
 * ----------------------------------------------------------------
 */
void
ExecEndHashJoin(HashJoinState *node)
{
	/*
	 * Free hash table
	 */
	if (node->hj_OuterHashTable)
	{
		ExecHashTableDestroy(node->hj_OuterHashTable);
		node->hj_OuterHashTable = NULL;
	}
	if (node->hj_InnerHashTable)
	{
		ExecHashTableDestroy(node->hj_InnerHashTable);
		node->hj_InnerHashTable = NULL;
	}
    
	/*
	 * Free the exprcontext
	 */
	ExecFreeExprContext(&node->js.ps);
    
	/*
	 * clean out the tuple table
	 */
	ExecClearTuple(node->js.ps.ps_ResultTupleSlot);
	ExecClearTuple(node->js.ps.ps_InnerTupleSlot); //CSI3130
	ExecClearTuple(node->js.ps.ps_OuterTupleSlot); //CSI3130
	ExecClearTuple(node->hj_OuterTupleSlot);
	ExecClearTuple(node->hj_InnerTupleSlot);//CSI3130
	ExecClearTuple(node->hj_InnerHashTupleSlot);
	ExecClearTuple(node->hj_OuterHashTupleSlot);//CSI3130
    
	/*
	 * clean up subtrees
	 */
	ExecEndNode(outerPlanState(node));
	ExecEndNode(innerPlanState(node));
}

/*
 * ExecHashJoinOuterGetTuple
 *
 *		get the next outer tuple for hashjoin: either by
 *		executing a plan node in the first pass, or from
 *		the temp files for the hashjoin batches.
 *
 * Returns a null slot if no more outer tuples.  On success, the tuple's
 * hash value is stored at *hashvalue --- this is either originally computed,
 * or re-read from the temp file.
 */
static TupleTableSlot *
ExecHashJoinOuterGetTuple(PlanState *outerNode,
						  HashJoinState *hjstate,
						  uint32 *hashvalue)
{
	HashJoinTable hashtable = hjstate->hj_InnerHashTable;//CSI3130
	int			curbatch = hashtable->curbatch;
	TupleTableSlot *slot;
    
	if (curbatch == 0)
	{							/* if it is the first pass */
        
		/*
		 * Check to see if first outer tuple was already fetched by
		 * ExecHashJoin() and not used yet.
		 */
		slot = hjstate->hj_FirstOuterTupleSlot;
		if (!TupIsNull(slot))
			hjstate->hj_FirstOuterTupleSlot = NULL;
		else
			slot = ExecProcNode(outerNode);
		if (!TupIsNull(slot))
		{
			/*
			 * We have to compute the tuple's hash value.
			 */
			ExprContext *econtext = hjstate->js.ps.ps_ExprContext;
            
			econtext->ecxt_outertuple = slot;
			*hashvalue = ExecHashGetHashValue(hashtable, econtext,
											  hjstate->hj_OuterHashKeys);
            
			/* remember outer relation is not empty for possible rescan */
			hjstate->hj_OuterNotEmpty = true;
            
			return slot;
		}
        
		/*
		 * We have just reached the end of the first pass. Try to switch to a
		 * saved batch.
		 */
		curbatch = ExecHashJoinNewBatch(hjstate);
	}
    
	/*
	 * Try to read from a temp file. Loop allows us to advance to new batches
	 * as needed.  NOTE: nbatch could increase inside ExecHashJoinNewBatch, so
	 * don't try to optimize this loop.
	 */
	while (curbatch < hashtable->nbatch)
	{
		slot = ExecHashJoinGetSavedTuple(hjstate,
										 hashtable->outerBatchFile[curbatch],
										 hashvalue,
										 hjstate->hj_OuterTupleSlot);
		if (!TupIsNull(slot))
			return slot;
		curbatch = ExecHashJoinNewBatch(hjstate);
	}
    
	/* Out of batches... */
	return NULL;
}

/*
 * ExecHashJoinNewBatch
 *		switch to a new hashjoin batch
 *
 * Returns the number of the new batch (1..nbatch-1), or nbatch if no more.
 * We will never return a batch number that has an empty outer batch file.
 */
static int
ExecHashJoinNewBatch(HashJoinState *hjstate)
{
	HashJoinTable hashtable = hjstate->hj_InnerHashTable;//CSI3130
	int			nbatch;
	int			curbatch;
	BufFile    *innerFile;
	TupleTableSlot *slot;
	uint32		hashvalue;
    
start_over:
	nbatch = hashtable->nbatch;
	curbatch = hashtable->curbatch;
    
	if (curbatch > 0)
	{
		/*
		 * We no longer need the previous outer batch file; close it right
		 * away to free disk space.
		 */
		if (hashtable->outerBatchFile[curbatch])
			BufFileClose(hashtable->outerBatchFile[curbatch]);
		hashtable->outerBatchFile[curbatch] = NULL;
	}
    
	/*
	 * We can always skip over any batches that are completely empty on both
	 * sides.  We can sometimes skip over batches that are empty on only one
	 * side, but there are exceptions:
	 *
	 * 1. In a LEFT JOIN, we have to process outer batches even if the inner
	 * batch is empty.
	 *
	 * 2. If we have increased nbatch since the initial estimate, we have to
	 * scan inner batches since they might contain tuples that need to be
	 * reassigned to later inner batches.
	 *
	 * 3. Similarly, if we have increased nbatch since starting the outer
	 * scan, we have to rescan outer batches in case they contain tuples that
	 * need to be reassigned.
	 */
	curbatch++;
	while (curbatch < nbatch &&
		   (hashtable->outerBatchFile[curbatch] == NULL ||
			hashtable->innerBatchFile[curbatch] == NULL))
	{
		if (hashtable->outerBatchFile[curbatch] &&
			hjstate->js.jointype == JOIN_LEFT)
			break;				/* must process due to rule 1 */
		if (hashtable->innerBatchFile[curbatch] &&
			nbatch != hashtable->nbatch_original)
			break;				/* must process due to rule 2 */
		if (hashtable->outerBatchFile[curbatch] &&
			nbatch != hashtable->nbatch_outstart)
			break;				/* must process due to rule 3 */
		/* We can ignore this batch. */
		/* Release associated temp files right away. */
		if (hashtable->innerBatchFile[curbatch])
			BufFileClose(hashtable->innerBatchFile[curbatch]);
		hashtable->innerBatchFile[curbatch] = NULL;
		if (hashtable->outerBatchFile[curbatch])
			BufFileClose(hashtable->outerBatchFile[curbatch]);
		hashtable->outerBatchFile[curbatch] = NULL;
		curbatch++;
	}
    
	if (curbatch >= nbatch)
		return curbatch;		/* no more batches */
    
	hashtable->curbatch = curbatch;
    
	/*
	 * Reload the hash table with the new inner batch (which could be empty)
	 */
	ExecHashTableReset(hashtable);
    
	innerFile = hashtable->innerBatchFile[curbatch];
    
	if (innerFile != NULL)
	{
		if (BufFileSeek(innerFile, 0, 0L, SEEK_SET))
			ereport(ERROR,
					(errcode_for_file_access(),
                     errmsg("could not rewind hash-join temporary file: %m")));
        
		while ((slot = ExecHashJoinGetSavedTuple(hjstate,
												 innerFile,
												 &hashvalue,
												 hjstate->hj_InnerHashTupleSlot)))//CSI3130
		{
			/*
			 * NOTE: some tuples may be sent to future batches.  Also, it is
			 * possible for hashtable->nbatch to be increased here!
			 */
			ExecHashTableInsert(hashtable,
								ExecFetchSlotTuple(slot),
								hashvalue);
		}
        
		/*
		 * after we build the hash table, the inner batch file is no longer
		 * needed
		 */
		BufFileClose(innerFile);
		hashtable->innerBatchFile[curbatch] = NULL;
	}
    
	/*
	 * If there's no outer batch file, advance to next batch.
	 */
	if (hashtable->outerBatchFile[curbatch] == NULL)
		goto start_over;
    
	/*
	 * Rewind outer batch file, so that we can start reading it.
	 */
	if (BufFileSeek(hashtable->outerBatchFile[curbatch], 0, 0L, SEEK_SET))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not rewind hash-join temporary file: %m")));
    
	return curbatch;
}

/*
 * ExecHashJoinSaveTuple
 *		save a tuple to a batch file.
 *
 * The data recorded in the file for each tuple is its hash value,
 * then an image of its HeapTupleData (with meaningless t_data pointer)
 * followed by the HeapTupleHeader and tuple data.
 *
 * Note: it is important always to call this in the regular executor
 * context, not in a shorter-lived context; else the temp file buffers
 * will get messed up.
 */
void
ExecHashJoinSaveTuple(HeapTuple heapTuple, uint32 hashvalue,
					  BufFile **fileptr)
{
	BufFile    *file = *fileptr;
	size_t		written;
    
	if (file == NULL)
	{
		/* First write to this batch file, so open it. */
		file = BufFileCreateTemp(false);
		*fileptr = file;
	}
    
	written = BufFileWrite(file, (void *) &hashvalue, sizeof(uint32));
	if (written != sizeof(uint32))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));
    
	written = BufFileWrite(file, (void *) heapTuple, sizeof(HeapTupleData));
	if (written != sizeof(HeapTupleData))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));
    
	written = BufFileWrite(file, (void *) heapTuple->t_data, heapTuple->t_len);
	if (written != (size_t) heapTuple->t_len)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not write to hash-join temporary file: %m")));
}

/*
 * ExecHashJoinGetSavedTuple
 *		read the next tuple from a batch file.	Return NULL if no more.
 *
 * On success, *hashvalue is set to the tuple's hash value, and the tuple
 * itself is stored in the given slot.
 */
static TupleTableSlot *
ExecHashJoinGetSavedTuple(HashJoinState *hjstate,
						  BufFile *file,
						  uint32 *hashvalue,
						  TupleTableSlot *tupleSlot)
{
	HeapTupleData htup;
	size_t		nread;
	HeapTuple	heapTuple;
    
	nread = BufFileRead(file, (void *) hashvalue, sizeof(uint32));
	if (nread == 0)
		return NULL;			/* end of file */
	if (nread != sizeof(uint32))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	nread = BufFileRead(file, (void *) &htup, sizeof(HeapTupleData));
	if (nread != sizeof(HeapTupleData))
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	heapTuple = palloc(HEAPTUPLESIZE + htup.t_len);
	memcpy((char *) heapTuple, (char *) &htup, sizeof(HeapTupleData));
	heapTuple->t_datamcxt = CurrentMemoryContext;
	heapTuple->t_data = (HeapTupleHeader)
    ((char *) heapTuple + HEAPTUPLESIZE);
	nread = BufFileRead(file, (void *) heapTuple->t_data, htup.t_len);
	if (nread != (size_t) htup.t_len)
		ereport(ERROR,
				(errcode_for_file_access(),
				 errmsg("could not read from hash-join temporary file: %m")));
	return ExecStoreTuple(heapTuple, tupleSlot, InvalidBuffer, true);
}


void
ExecReScanHashJoin(HashJoinState *node, ExprContext *exprCtxt)
{
	/*
	 * In a multi-batch join, we currently have to do rescans the hard way,
	 * primarily because batch temp files may have already been released. But
	 * if it's a single-batch join, and there is no parameter change for the
	 * inner subnode, then we can just re-use the existing hash table without
	 * rebuilding it.
	 */
    elog(17,  "rescan called\n");//CSI3130
	if (node->hj_InnerHashTable != NULL)//CSI3130
	{
		if (node->hj_InnerHashTable->nbatch == 1 &&//CSI3130
			((PlanState *) node)->righttree->chgParam == NULL)
		{
			/*
			 * okay to reuse the hash table; needn't rescan inner, either.
			 *
			 * What we do need to do is reset our state about the emptiness
			 * of the outer relation, so that the new scan of the outer will
			 * update it correctly if it turns out to be empty this time.
			 * (There's no harm in clearing it now because ExecHashJoin won't
			 * need the info.  In the other cases, where the hash table
			 * doesn't exist or we are destroying it, we leave this state
			 * alone because ExecHashJoin will need it the first time
			 * through.)
			 */
			node->hj_OuterNotEmpty = false;
		}
		else
		{
			/* must destroy and rebuild hash table */
			ExecHashTableDestroy(node->hj_InnerHashTable);
			node->hj_InnerHashTable = NULL;
			node->hj_OuterHashTable = NULL;
            
			/*
			 * if chgParam of subnode is not null then plan will be re-scanned
			 * by first ExecProcNode.
			 */
			if (((PlanState *) node)->righttree->chgParam == NULL)
				ExecReScan(((PlanState *) node)->righttree, exprCtxt);
		}
	}
    
	/* Always reset intra-tuple state */
	node->hj_OuterCurHashValue = 0;
	node->hj_InnerCurBucketNo = 0;
	node->hj_InnerCurTuple = NULL;
    
	node->js.ps.ps_OuterTupleSlot = NULL;
	node->js.ps.ps_TupFromTlist = false;
	node->hj_NeedNewOuter = true;
	node->hj_MatchedOuter = false;
	node->hj_FirstOuterTupleSlot = NULL;
    
	/*
	 * if chgParam of subnode is not null then plan will be re-scanned by
	 * first ExecProcNode.
	 */
	if (((PlanState *) node)->lefttree->chgParam == NULL)
		ExecReScan(((PlanState *) node)->lefttree, exprCtxt);
}
