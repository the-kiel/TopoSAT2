/*****************************************************************************************[Cooperation.h]
 * Copyright (c) 2008-20011, Youssef Hamadi, Saïd Jabbour and Lakhdar Saïs
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 * associated documentation files (the "Software"), to deal in the Software without restriction,
 * including without limitation the rights to use, copy, modify, merge, publish, distribute,
 * sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or
 * substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 * NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 * DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 * OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *******************************************************************************************/
#include "core/Cooperation.h"


namespace Glucose {

/*_________________________________________________________________________________________________
   *    |
   *    |  exportExtraUnit : ()  ->  [void]
   *    |  Description : manage export Extra Unit Clauses
   *    |  Returns true if the clause was exported successfully, and false otherwise
   *    |________________________________________________________________________________________________@*/

bool Cooperation::exportExtraUnit(int id, Lit unit){
    // TODO: CHECKTHIS (UNIT_EXCHANGE)
    // new: Send this unit clause only to the communication thread, not to other solvers!
    int ind = tailExtraUnits_comThread[id];
    if(((ind + 1)%MAX_EXTRA_UNITS) == headExtraUnits_comThread[id]){
        return false;
    }
    else{
        extraUnitInBuffer_comThread[id][ind++].x = unit.x;
        if(ind == MAX_EXTRA_UNITS)
            ind=0;
        tailExtraUnits_comThread[id]=ind;
    }
    return true;
}

/*_________________________________________________________________________________________________
   *    |
   *    |  importExtraUnits : ()  ->  [void]
   *    |  Description : store unit extra clause in the vector unit_learnts
   *    |________________________________________________________________________________________________@*/

void Cooperation::importExtraUnits(Solver* s, vec<Lit>& unit_learnts){
    // TODO: CHECKTHIS (UNIT_EXCHANGE)
    int id = s->threadId;
    
    // New: Only read units from the communication thread!
    
    int head = headExtraUnits_solvers[id];
    int tail = tailExtraUnits_solvers[id];
    if(head == tail)
        return;
    int end = tail;
    if(tail < head)
        end = MAX_EXTRA_UNITS;
    for(int i = head ; i < end ; i++)
        storeExtraUnits(s, 0, extraUnitInBuffers_solvers[id][i], unit_learnts);
    if(tail < head){
        for(int i = 0 ; i < tail ; i++)
            storeExtraUnits(s, 0, extraUnitInBuffers_solvers[id][i], unit_learnts);
    }
    head = tail;
    if(head == MAX_EXTRA_UNITS)
        head = 0;
    headExtraUnits_solvers[id] = head;
    
}

/*_________________________________________________________________________________________________
   *    |
   *    |  importExtraUnits : ()  ->  [void]
   *    |  Description : manage import Extra Unit Clauses
   *    |________________________________________________________________________________________________@*/

//   void Cooperation::importExtraUnits(Solver* s){
//
//     int id = s->threadId;
//
//     for(int t = 0; t < nbThreads; t++){
//
//       if(t == id)
// 	continue;
//
//       int head = headExtraUnits[t][id];
//       int tail = tailExtraUnits[t][id];
//       if(head == tail)
// 	continue;
//
//       int end = tail;
//       if(tail < head) end = MAX_EXTRA_UNITS;
//
//       for(int i = head; i < end; i++)
// 	uncheckedEnqueue(s, t, extraUnits[t][id][i]);
//
//       if(tail < head)
// 	for(int i = 0; i < tail; i++)
// 	  uncheckedEnqueue(s, t, extraUnits[t][id][i]);
//
//       head = tail;
//       if(head == MAX_EXTRA_UNITS) head = 0;
//       headExtraUnits[t][id] = head;
//     }
//   }


/*_________________________________________________________________________________________________
   *    |
   *    |  uncheckedEnqueue : ()  ->  [void]
   *    |  Description: Enqueue the unit literals at level 0
   *    |________________________________________________________________________________________________@*/

void Cooperation::uncheckedEnqueue(Solver* s, int t, Lit l){
    
    if(s->value(l) == l_False) answers[s->threadId] = l_False;
    
    if(s->value(l) != l_Undef) return;
    s->uncheckedEnqueue(l);
    nbImportedExtraUnits[s->threadId]++;
}

/*_________________________________________________________________________________________________
   *    |
   *    |  uncheckedEnqueue : ()  ->  [void]
   *    |  Description: Enqueue the unit literals at level 0
   *    |________________________________________________________________________________________________@*/

void Cooperation::storeExtraUnits(Solver* s, int t, Lit l, vec<Lit>& unitLits){
    unitLits.push(l);
}

/*_________________________________________________________________________________________________
   *    |
   *    |  exportExtraClause : ()  ->  [void]
   *    |  Description: each time a new clause is learnt, it is exported to other threads
   *    |________________________________________________________________________________________________@*/


void Cooperation::exportExtraClause(int id, vec<Lit>& learnt, int lbd, int threadId, int index){

    if(learnt.size() > hard_limit_size  || lbd > hard_limit_lbd)
        return;
    int ranking = factor_lbd * lbd + factor_size * learnt.size();
    if(ranking > weightedExportLimit)
        return;
    for(int t = 0; t < nbBuffers; t++){

        if(((t == id)) )//|| (learnt.size() > pairwiseLimitExportClauses[id][t]))
            continue;

        int ind = tailExtraClauses[id][t];
        if(((ind+1) % MAX_EXTRA_CLAUSES) == headExtraClauses[id][t])
            continue;

        extraClauses[id][t][ind]    = new Lit [learnt.size() + SIZE_CLAUSE_HEADER];
        extraClauses[id][t][ind][0] = mkLit(learnt.size());
        extraClauses[id][t][ind][1] = mkLit(lbd);
        extraClauses[id][t][ind][2] = mkLit(threadId);
        extraClauses[id][t][ind][3] = mkLit(index);

        for(int j = 0; j < learnt.size(); j++)
            extraClauses[id][t][ind][j + SIZE_CLAUSE_HEADER] = learnt[j];

        ind++;
        if(ind == MAX_EXTRA_CLAUSES) ind = 0;
        tailExtraClauses[id][t] = ind;
    }
}

void Cooperation::getNumStoredClauses(int id, int & maxNum, int & sum){
    sum = 0;
    maxNum = 0;
    for(int t = 0; t < nbBuffers; t++){

        if(t == id)
            continue;

        int head = headExtraClauses[t][id];
        int tail = tailExtraClauses[t][id];
        int numHere = (tail - head + 1 + MAX_EXTRA_CLAUSES) % MAX_EXTRA_CLAUSES;
        if(numHere > maxNum)
            maxNum = numHere;
        sum += numHere;
    }
}

/*_________________________________________________________________________________________________
   *    |
   *    |  exportExtraClause : ()  ->  [void]
   *    |  Description: each time a new clause is learnt, it is exported to other threads
   *    |________________________________________________________________________________________________@*/

void Cooperation::exportExtraClause(int id, Clause& c, int threadId, int index){

    for(int t = 0; t < nbBuffers; t++){

        if((t == id))// || (c.size() > pairwiseLimitExportClauses[id][t]))
            continue;

        int ind = tailExtraClauses[id][t];
        if(((ind+1) % MAX_EXTRA_CLAUSES) == headExtraClauses[id][t])
            continue;

        extraClauses[id][t][ind]    = new Lit [c.size() + SIZE_CLAUSE_HEADER];
        extraClauses[id][t][ind][0] = mkLit(c.size());
        extraClauses[id][t][ind][1] = mkLit(c.lbd());
        extraClauses[id][t][ind][2] = mkLit(threadId);
        extraClauses[id][t][ind][3] = mkLit(index);

        for(int j = 0; j < c.size(); j++)
            extraClauses[id][t][ind][j + SIZE_CLAUSE_HEADER] = c[j];

        ind++;
        if(ind == MAX_EXTRA_CLAUSES) ind = 0;
        tailExtraClauses[id][t] = ind;
    }
}

/*_________________________________________________________________________________________________
   *    |
   *    |  importExtraClauses : ()  ->  [void]
   *    |  Description: import Extra clauses sent from other threads
   *    |_______________________________________________________________________________________________@*/

void Cooperation::importExtraClauses(Solver* s){
    
    int id = s->threadId;
    
    for(int t = 0; t < nbBuffers; t++){

        if(t == id)
            continue;

        int head = headExtraClauses[t][id];
        int tail = tailExtraClauses[t][id];
        if(head == tail)
            continue;

        int end = tail;
        if(tail < head) end = MAX_EXTRA_CLAUSES;

        for(int i = head; i < end; i++)
            addExtraClause(s, t, extraClauses[t][id][i]);

        if(tail < head)
            for(int i = 0; i < tail; i++)
                addExtraClause(s, t, extraClauses[t][id][i]);
        
        head = tail;
        if(head == MAX_EXTRA_CLAUSES) head = 0;
        headExtraClauses[t][id] = head;
    }
}


// TODO:
// - how should I set LBD here? size? or transferred LBD?
// - Is it okay to set "canBeDel" to true immediately?
/*_________________________________________________________________________________________________
   *    |
   *    |  addExtraClause : ()  ->  [void]
   *    |  Description: build a clause from the learnt Extra Lit*
   *    |  watch it correctly, test basic cases distinguich other cases during watching process
   *    |________________________________________________________________________________________________@*/


void Cooperation::addExtraClause(Solver* s, int t, Lit* lt){
    
    vec<Lit>  extra_clause;
    vec<Lit> selectors;
    int       extra_backtrack_level = 0;
    int id   = s->threadId;
    int size = var(lt[0]);
    //int lbd  = var(lt[1]);
    int learntBy = var(lt[2]);
    int clauseIndex = var(lt[3]);
    int    wtch = 0;
    //Lit q = lit_Undef;
    //bool useOneWatched = false;
    for(int i = SIZE_CLAUSE_HEADER, j = 0; i < size+SIZE_CLAUSE_HEADER; i++) {
        Lit q = lt[i];
        if(s->value(q) == l_False && s->level(var(q)) == 0)
            continue;
        extra_clause.push(q);
        if(s->value(q) != l_False && wtch < 2){
            extra_clause[j] = extra_clause[wtch];
            extra_clause[wtch++] = q;
        }else if(s->level(var(q)) >= extra_backtrack_level)
            extra_backtrack_level = s->level(var(q));
        j++;
    }
    
    
    //conflict clause at level 0 --> formula is UNSAT
    if(extra_clause.size() == 0)
        setAnswer(id, l_False);
    
    // case of unit extra clause
    else if(extra_clause.size() == 1){
        s->cancelUntil(0);
        if(s->value(extra_clause[0]) == l_Undef){
            s->uncheckedEnqueue(extra_clause[0]);
            CRef cs = s->propagate();
            if(cs != CRef_Undef) answers[id] = l_False;
        }
    }
    
    else {
        // build clause from lits and add it to learnts(s) base
        // If clause is in conflicting state, add it one two-watched state. Otherwise: one-watched?
        // TODO: Can I import this in one-watched if a propagation / conflict is pending?
        bool oneWatched = oneWatchedImport && wtch == 1 && s->value(extra_clause[0]) == l_Undef;

        if(oneWatched){
            CRef cr = s->addExtraClause(extra_clause, oneWatched, learntBy, clauseIndex);
        }
       else{
            CRef cr = s->addExtraClause(extra_clause, false, learntBy, clauseIndex);

            // Case of Unit propagation: literal to propagate or bad level
            if(wtch == 1 && (s->value(extra_clause[0]) == l_Undef || extra_backtrack_level < s->level(var(extra_clause[0])))){
                s->cancelUntil(extra_backtrack_level);
                s->uncheckedEnqueue(extra_clause[0], cr);
            }

            // Case of Conflicting Extra Clause --> analyze that conflict
            else if(wtch == 0) {
                extra_clause.clear();
                selectors.clear();
                s->cancelUntil(extra_backtrack_level);
                unsigned int lbd;
                unsigned int szWithoutSelectors;

                s->analyze(cr, extra_clause, selectors, extra_backtrack_level, lbd, szWithoutSelectors);
                s->cancelUntil(extra_backtrack_level);
                s->conflicts++;
                // analyze lead to unit clause
                if(extra_clause.size() == 1){
                    assert(extra_backtrack_level == 0);
                    if(s->value(extra_clause[0]) == l_Undef)s->uncheckedEnqueue(extra_clause[0]);
                }
                // analyze lead to clause with size > 1
                else {
                    CRef cs = s->addExtraClause(extra_clause, false, s->threadId, s->conflicts);
                    s->uncheckedEnqueue(extra_clause[0], cs);
                }
            }
        }
    }
    
    nbImportedExtraClauses[id]++;
    
    
    delete [] lt;
}




/*_________________________________________________________________________________________________
   *    |
   *    |  addExtraClause : ()  ->  [void]
   *    |  Description: watch lits correctly and testing basic cases and
   *    |  build a clause from the learnt Extra Lit*
   *    |________________________________________________________________________________________________@*/

// void Cooperation::addExtraClause1(Solver* s, int t, Lit* lt){
//
//   int id = s->threadId;
//   int size = var(lt[0]);
//
//   vec<Lit> lits;
//   int j = 0;
//   int k = 0;
//   Lit q        = lit_Undef;
//   int maxLevel = 0;
//
//   for(int i=1; i < size+1; i++) {
//     Lit q = lt[i];
//     if(s->value(q) == l_False && s->level(var(q)) == 0)
// continue;
//     lits.push(lt[i]);
//     if(s->value(q) != l_False){
// lits[k]   = lits[j];
// lits[j++] = q;
//     }else if(s->level(var(q)) >= maxLevel)
// maxLevel = s->level(var(q));
//     k++;
//   }
//
//   //conflict clause at level 0
//   if(lits.size() == 0)
//     setAnswer(id, l_False);
//
//   // case of unit extra clause
//   else if(lits.size() == 1){
//     s->cancelUntil(0);
//     if(s->value(lits[0]) == l_Undef)s->uncheckedEnqueue(lits[0]);
//   }
//   else {
//     // build clause from lits
//     s->addExtraClause(lits);
//   }
//
//   nbImportedExtraClauses[id]++;
//   pairwiseImportedExtraClauses[t][id]++;
//
//   delete [] lt;
// }
//
//
// /*_________________________________________________________________________________________________
//   |
//   |  addExtraClause : ()  ->  [void]
//   |  Description: build a clause from the learnt Extra Lit*
//   |________________________________________________________________________________________________@*/
//
// void Cooperation::addExtraClause2(Solver* s, int t, Lit* lt){
//
//   int id = s->threadId;
//   int size = var(lt[0]);
//   vec<Lit> lits;
//
//   for(int i=1; i < size+1; i++)
//     lits.push(lt[i]);
//
//   // build clause from lits
//   s->addExtraClause(lits);
//
//   nbImportedExtraClauses[id]++;
//   pairwiseImportedExtraClauses[t][id]++;
//
//   delete [] lt;
// }

/*_________________________________________________________________________________________________
   *    |
   *    |  updateLimitExportClauses : ()  ->  [void]
   *    |  update limit size of exported clauses in order to maintain exchange during search:
   *    |  (MAX_IMPORT_CLAUSES / LIMIT_CONFLICTS) is the percent of clauses that must be shared
   *    |________________________________________________________________________________________________@*/


// void Cooperation::updateLimitExportClauses(Solver* s){
//
//   int id = s->threadId;
//
//   if((int)s->conflicts % LIMIT_CONFLICTS_EVAL != 0) return;
//
//   double sumExtImpCls = 0;
//
//   for(int t = 0; t < nbThreads; t++)
//     sumExtImpCls += pairwiseImportedExtraClauses[t][id];
//
//   switch(ctrl){
//
//   case 1 :{
//     if(sumExtImpCls <= MAX_IMPORT_CLAUSES)
// or(int t = 0; t < nbThreads; t++)
//  pairwiseLimitExportClauses[t][id]+=1;
//     else
// or(int t = 0; t < nbThreads; t++)
//  pairwiseLimitExportClauses[t][id]-=1;
//
//     for(int t = 0; t < nbThreads; t++)
// airwiseImportedExtraClauses[t][id] = 0;
//     break;
//   }
//
//
//   case 2 :{
//     if(sumExtImpCls <= MAX_IMPORT_CLAUSES)
// or(int t = 0; t < nbThreads; t++)
//  pairwiseLimitExportClauses[t][id] += aimdy / pairwiseLimitExportClauses[t][id];
//     else
// or(int t = 0; t < nbThreads; t++)
//  pairwiseLimitExportClauses[t][id] -= aimdx * pairwiseLimitExportClauses[t][id];
//
//     for(int t = 0; t < nbThreads; t++)
// airwiseImportedExtraClauses[t][id] = 0;
//     break;
//   }
//   }
// }

/*_________________________________________________________________________________________________
   *    |
   *    |  printStats : ()  ->  [void]
   *    |  Description: print statistics of each thread
   *    |________________________________________________________________________________________________@*/

void Cooperation::printStats(int& id){
    
    uint64_t nbSharedExtraClauses = 0;
    uint64_t nbSharedExtraUnits   = 0;
    uint64_t totalConflicts       = 0;
    
    for(int t = 0; t < nbThreads; t++){

        nbSharedExtraClauses += nbImportedExtraClauses[t];
        nbSharedExtraUnits   += nbImportedExtraUnits  [t];
        totalConflicts += solvers[t].conflicts;
    }
    
    
    printf(" -----------------------------------------------------------------------------------------------------------------------\n");
    printf("| ManySAT 2.2 - all threads statistics           DETERMINISTIC MODE ? %s              initial limit export clauses : %3d |\n",
           deterministic_mode == true ? "Y" : "N",
           limitExportClauses);
    printf("|-----------------------------------------------------------------------------------------------------------------------|\n");
    printf("|  Thread  | winner  |   #restarts   |   decisions   |  #conflicts   |   %% shared cls  |  #extra units | #extra clauses |         \n");
    printf("|----------|---------|---------------|---------------|---------------|-----------------|---------------|----------------|\n");
    
    for(int t = 0; t < nbThreads; t++)
        printf("| %8d | %7s | %13d | %13d | %13d | %13d %% | %13d | %14d |\n",
               t,
               t==id?"x":" ",
               (int)solvers[t].starts,
               (int)solvers[t].decisions,
               (int)solvers[t].conflicts,
               (int)solvers[t].conflicts==0 ? 0 : (int) (nbImportedExtraUnits[t] + nbImportedExtraClauses[t]) * 100 / (int)solvers[t].conflicts,
               (int)nbImportedExtraUnits[t],
               (int)nbImportedExtraClauses[t]);


    printf("|----------------------------------------------------|---------------|-----------------|---------------|----------------|\n");
    printf("|                                                    | %13d | %13d %% | %13d | %14d |\n",
           (int)totalConflicts,
           (int)totalConflicts==0 ? 0 : (int) (nbSharedExtraUnits + nbSharedExtraClauses) * 100 / (int)totalConflicts,
           (int)nbSharedExtraUnits,
           (int)nbSharedExtraClauses);
    printf(" -----------------------------------------------------------------------------------------------------------------------\n");

    Parallel_Info();

}


/*_________________________________________________________________________________________________
   *    |
   *    |  printExMatrix : ()  ->  [void]
   *    |  Description: print the final values of size clauses shared between parwise threads
   *    |________________________________________________________________________________________________@*/

// void Cooperation::printExMatrix(){
//
//   printf("\n Final Matrix extra shared clauses limit size \n");
//   printf(" ----------------------------------------------------\n");
//   for(int i = 0; i < nbThreads; i++){
//     printf("|");
//     for(int j = 0; j < nbThreads; j++)
// f(i != j)
//  printf(" e(%d,%d)=%3d  ", i, j, (int)pairwiseLimitExportClauses[i][j]);
// lse
//  printf(" e(%d,%d)=%3d  ", i, j, 0);
//     printf(" |\n");
//   }
//   printf(" ----------------------------------------------------\n\n");
// }


/*_________________________________________________________________________________________________
   *    |
   *    |  Parallel_Info : ()  ->  [void]
   *    |  Description: more informations about deterministic or non deterministic mode and final matrix print
   *    |________________________________________________________________________________________________@*/

void Cooperation::Parallel_Info(){
    printf(" DETERMINISTIC_MODE? : %s \n", (deterministic_mode == true ? "YES" : "NO"));
    printf(" CONTROL POLICY?	 : %s  \n", (ctrl != 0 ? (ctrl==1 ? "DYNAMIC (INCREMENTAL  en= +- 1)" : "DYNAMIC (AIMD: en=  en - a x en, en + b/en)") : "STATIC (fixed Limit Export Clauses)"));
    if(ctrl == 0)
        printf(" LIMIT EXPORT CLAUSES (PAIRWISE) : [identity] x %d\n\n", limitExportClauses);
    //else
    //printExMatrix();
}

void Cooperation::MPI_exportUnitClause(Lit l){
    if(units_send.count(toInt(l)) == 0){
        units_send.insert(toInt(l));
        MPI_out_queue_units.push_back(l);
    }
}

struct compExportClauses{
    int factor_lbd;
    int factor_size;
    compExportClauses(int _fac_lbd, int _fac_size) : factor_lbd(_fac_lbd), factor_size(_fac_size) {    }
    bool operator()(const std::vector<int> & v1, const std::vector<int> & v2){
        return v1[0]*factor_lbd+v1[1] < v2[0]*factor_lbd+v2[1];
    }
};
///////////////////////////////////////////////////////////////////////
// TODO: Adjust number of neighbours here?
void Cooperation::MPI_send_data(double productionRate){
    if(exportPolicy == EXPORT_DYNAMIC_DEGREE &&  productionRate <= 0)
        return;
    int other_clauses_sizes = 0;
    for(int i = 0 ; i < MPI_out_queue_clauses.size();i++)
        other_clauses_sizes += MPI_out_queue_clauses[i].size();
    int size_to_send = MPI_out_queue_units.size() + 1 +  other_clauses_sizes;
    numClausesSent += MPI_out_queue_clauses.size();
    numLiteralsSent += other_clauses_sizes;
    if(size_to_send <= 1)
        return;
    int * message = (int*) malloc(size_to_send * sizeof(int));
    assert(message && "Could not allocate MPI send buffer! ");

    /************************************************
     *  Section for unit clauses
     */
    message[0] = MPI_out_queue_units.size();
    int index = 1;
    for(int i = 0 ; i < MPI_out_queue_units.size();i++)
        message[index++] = toInt(MPI_out_queue_units[i]);
    
    /************************************************
     *  Section for other clauses
     */
    
    for(int i = 0 ; i < MPI_out_queue_clauses.size();i++){
        std::vector<int>&v=MPI_out_queue_clauses[i];
        for(int j = 0 ; j < v.size();j++)
            message[index++]=v[j];
    }
    assert(index == size_to_send);
    /* Send the data! */
    
    int degree = numProcesses-1;
    if(exportPolicy == EXPORT_FIX_DEGREE_FIX_THRESHOLD)
        degree = numNeighbours;
    else if (exportPolicy == EXPORT_DYNAMIC_DEGREE || exportPolicy == EXPORT_LAZY_EXCHANGE)
        degree = ((int) ceil((double) target_exportClauses/productionRate)) ;
    
    for(int i = 1 ; i < numProcesses ; i++){
        int target = (procId+i)%numProcesses;
        assert(target >= 0);
        assert(target < numProcesses);
        assert(target != procId);
        int size_here= (i <= degree) ? size_to_send : (1+MPI_out_queue_units.size());
        send_wrapper(message, size_here, MPI_INT, target, LEARNT_CLAUSE_TAG, MPI_COMM_WORLD);
    }
    

    /************************************************
     * Clean up:
     */
    MPI_out_queue_units.clear();
    MPI_out_queue_clauses.clear();
    free(message);
    
    // Sort export-clauses
    // TODO: adjust export threshold
    // Create array, write stuff
    // Send the package to the neighbours
}

// TODO: Dynamic adjust the limits on LBD/Size?
void Cooperation::MPI_store_export_clause(vec<Lit> & learnt, int lbd){
    // TODO: should I always store this, or only when the buffer is not too full?
    MPI_out_queue_clauses.push_back(std::vector<int>());
    std::vector<int> &toFill = MPI_out_queue_clauses.back();
    toFill.reserve(2+learnt.size());
    toFill.push_back(learnt.size());
    toFill.push_back(lbd);
    for(int i = 0 ; i < learnt.size();i++)
        toFill.push_back(toInt(learnt[i]));
}

void Cooperation::updateThreshold(int recvInternal, double timeSinceLastUpdate){
    if (timeSinceLastUpdate < 1e-2)
        return;
    switch(exportPolicy){
    case EXPORT_DYNAMIC_THRESHOLD:
    case EXPORT_DYNAMIC_THRESHOLD_DEGREE_INDEPENDET:
    {
        double currentProductionRate = (exportPolicy == EXPORT_DYNAMIC_THRESHOLD) ? ( (recvInternal * (numProcesses-1)) / timeSinceLastUpdate) : (recvInternal / timeSinceLastUpdate);
        double diff = target_exportClauses - currentProductionRate;
        // Adjust the limit:
        weightedExportLimit = weightedExportLimit + 0.05*diff;
        if(weightedExportLimit > factor_lbd * hard_limit_lbd + factor_size*hard_limit_size)
            weightedExportLimit = factor_lbd * hard_limit_lbd + factor_size*hard_limit_size;
        bool debug = false;
        if(debug)
            printf("c process %d updating threshold to %d\n", procId,  weightedExportLimit);

    }
        break;

    default:
        break;
    }
}

void Cooperation::communicationThread(double shutdown_time){
    // Sleep a bit, depending on the process id
    //double startupTime = MPI_Wtime();
    double timeLastReceive = MPI_Wtime();
    double timeLastCheckedStats = MPI_Wtime();
    //double time_next_unit_check = MPI_Wtime()+5;
    unitsReceived=0;
    int first_sleep = (comCycleTime * procId * 100) / numProcesses;
    usleep(first_sleep);
    bool done = false;
    int iterationsBetweenSends = 10;
    int sleep_time = comCycleTime * 1000 / iterationsBetweenSends;
    int iterations = 0;
    int numCounts = 0;
    double low_pass_clause_production_rate = 0.0;
    bool start_counting = false;
    double time_last_steal = MPI_Wtime();
    //bool useCNC = false;         // TODO: Make this a parameter!
    if(useCNC && procId == 0){
        master_OpenJobs.push_back(std::vector<int>());
    }
    
    while(!done){
        iterations++;
        lbool current_status = checkStatus();
        if(current_status != l_Undef){
            // Write answer, terminate
            printf("c com thread read answer! \n");
            int result = (current_status == l_True) ? 1 : 0;
            for(int i = 0 ; i < numProcesses ; i++){
                if(i != procId)
                    send_wrapper(&result, 1, MPI_INT, i, REPORT_TAG, MPI_COMM_WORLD);
            }
            for(int i = 0 ; i < nbThreads ; i++)
                solvers[i].interrupt();
            done = true;
        }
        if(interrupted){
            printf("c solver was interrupted...\n");
            return;
        }


        int recv = readInternalBuffer();
        if(recv > 0)
            start_counting = true;

        lbool globalStatus = readIncomingMessages();
        if(globalStatus != l_Undef){
            done = true;
            break;
        }
        /* ========================================================================
        // Check for timeout */
        if(MPI_Wtime() > shutdown_time){
            for(int i = 0 ; i < nbThreads ; i++)
                solvers[i].interrupt();
            interrupted = true;
        }

        /* ========================================================================
        // If lazy clause exchange is used, read buffers to see if some clauses
        // were used and may be exported now */
        if(exportPolicy == EXPORT_LAZY_EXCHANGE)
            recv = readUsageBuffers();


        double curr_receive_rate = (MPI_Wtime() > timeLastCheckedStats+1e-3) ? recv/(MPI_Wtime()-timeLastReceive) : recv;
        if(start_counting){
            if(numCounts < 20){
                low_pass_clause_production_rate = (1-1.0/((double)numCounts+1))*low_pass_clause_production_rate + (1.0/(numCounts+1))*curr_receive_rate;
            }
            else{
                low_pass_clause_production_rate = 0.95*low_pass_clause_production_rate + 0.05*curr_receive_rate;
            }
            numCounts++;
        }
        readDeletedBuffers();
        updateThreshold(recv, MPI_Wtime()-timeLastReceive);
        timeLastReceive = MPI_Wtime();
        if(!done && iterations % iterationsBetweenSends == 0){
            MPI_send_data(low_pass_clause_production_rate);
        }
        if(useCNC){
            readCubeConquerBuffers();
            master_organize_cnc(time_last_steal);
        }
        usleep(sleep_time);

    }
#ifdef GLOBAL_DEBUG
    printf("c communication thread of process %d terminating! \n", procId);
#endif
}

void Cooperation::handleNewUnit(Lit l, bool fromInside){

    if(knownUnits.count(toInt(l)) == 0){
        unitsReceived++;
        knownUnits.insert(toInt(l));
        // Send it to all other solver threads:
        for(int i = 0 ; i < nbThreads ; i++){
            int ind = tailExtraUnits_solvers[i];
            if(((ind+1)%MAX_EXTRA_UNITS) == headExtraUnits_solvers[i]){
                //                 printf("c com-thread trying to send units to solver %d, but the buffer is full! (ind=%d) \n", i, ind);
            }
            else{
                extraUnitInBuffers_solvers[i][ind++].x = l.x;
                if(ind == MAX_EXTRA_UNITS)
                    ind = 0;
                tailExtraUnits_solvers[i]=ind;
            }
        }
        if(fromInside){
            // Also send it to other solver processes!
            MPI_out_queue_units.push_back(l);
        }
    }
}


void Cooperation::lazyStoreClauses(Lit * l){
    int size = var(l[0]);
    int lbd = var(l[1]);
    int sender_thread = var(l[2]);
    int index = var(l[3]);
    assert(lazyClauseStorage.count(std::make_pair(sender_thread, index)) == 0);

    std::vector<int> tmp;
    tmp.push_back(size);
    tmp.push_back(lbd);
    tmp.push_back(sender_thread);
    tmp.push_back(index);
    for(int i = 0 ; i < size ; i++)
        tmp.push_back(toInt(l[i+SIZE_CLAUSE_HEADER]));
    lazyClauseStorage[std::make_pair(sender_thread, index)]=tmp;

}

/********************
   * The commmunication-thread handles clauses received from its shared-memory-solver.
   * Depending on the clause exhange policy, this is either stored, or written to the MPI buffer immediately.
   * */
void Cooperation::storeReceivedClause(Lit * l){
    switch(exportPolicy){
    case EXPORT_LAZY_EXCHANGE:
        lazyStoreClauses(l);
        break;
    default:
        storeClauseInMPIBuffer(l);
    }
    delete [] l;
}

/*
   * The communication thread reads shared memory buffers, and copies content to the MPI buffers
   * */
int Cooperation::readInternalBuffer(){
    int nbClausesImported = 0;
    vec<Lit> units2Forward;
    while(unitsReceivedFrom.size() < nbThreads)
        unitsReceivedFrom.push_back(std::set<int>());
    // Import unit clauses
    for(int t = 0 ; t < nbThreads ; t++){
        int head = headExtraUnits_comThread[t];
        int tail = tailExtraUnits_comThread[t];
        if(head == tail)
            continue;
        int end = tail;
        if(tail < head)
            end = MAX_EXTRA_UNITS;
        assert(head < end);
        for(int i = head ; i < end ; i++){
            handleNewUnit(extraUnitInBuffer_comThread[t][i], true);
            nbUnitsExported++;
        }
        if(tail < head){
            for(int i = 0 ; i < tail ; i++){
                handleNewUnit(extraUnitInBuffer_comThread[t][i], true);
                nbUnitsExported++;
            }
        }
        head = tail;
        if(head == MAX_EXTRA_UNITS)
            head=0;
        headExtraUnits_comThread[t]=head;
    }

    // Import other clauses
    for(int t = 0 ; t < nbThreads ; t++){
        int head = headExtraClauses[t][nbThreads];
        int tail = tailExtraClauses[t][nbThreads];
        if(head == tail)
            continue;
        int end = tail;
        if(tail < head) end = MAX_EXTRA_CLAUSES;

        for(int i = head; i < end; i++){
            nbClausesImported++;
            nbClausesExported++;
            storeReceivedClause(extraClauses[t][nbThreads][i]);
        }

        if(tail < head)
            for(int i = 0; i < tail; i++){
                nbClausesImported++;
                nbClausesExported++;
                storeReceivedClause(extraClauses[t][nbThreads][i]);
            }
        
        head = tail;
        if(head == MAX_EXTRA_CLAUSES) head = 0;
        headExtraClauses[t][nbThreads] = head;
    }
    return nbClausesImported;
}

lbool Cooperation::checkStatus(){
    for(int i = 0 ; i < nbThreads ; i++){
        if(answers[i] != l_Undef){
            return answers[i];
        }
    }
    return l_Undef;
}



lbool Cooperation::readIncomingMessages(){
    if(!useMPI)
        return l_Undef;
    MPI_Status s;
    int received;
    bool communication_done = false;
    lbool status = l_Undef;
    int messagesRead = 0;
    while(!communication_done){
        MPI_Iprobe(MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &received, &s);
        if(received){
            messagesRead++;
            switch(s.MPI_TAG){
            case REPORT_TAG:
            {
                // Read result, stop
                int ret;
                MPI_Recv(&ret, 1, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);

                globalResult = (ret == 1) ? l_True : l_False;
                printf("c received answer %d from %d , this was the %d-th message read in this iteration! \n", ret, s.MPI_SOURCE, messagesRead);
                status = ret? l_True : l_False;
                for(int i = 0 ; i < nbThreads ; i++)
                    solvers[i].interrupt();
                break;
            }
            case LEARNT_CLAUSE_TAG:
            {
                int length;
                MPI_Get_count(&s, MPI_INT, &length);
                // TODO: Does it make sense to allocate new memory every time, or should I have just one buffer?
                int * arr = (int*) malloc(sizeof(int) * length);
                MPI_Recv(arr, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
                handleReceivedClauses(arr, length);
                free(arr);
                break;
            }
            case SHUTDOWN_TAG:
                // TODO
                printf("c received shutdown flag, is this correct??? \n");
                break;
            case NEW_CUBES_FOR_MASTER_TAG:
                master_receive_new_cubes(s);
                break;
            case NEW_CUBE_FOR_SLAVE_TAG:
                comForwardCubes(s);
                break;
            case CUBE_FAILED_TAG:
                if (master_receive_failed_cube(s)){

                    status = l_False;
                    // Tell all others to terminate:
                    int ret = 0;
                    for(int i = 1 ; i < numProcesses ; i++)
                        send_wrapper(&ret, 1, MPI_INT, i, REPORT_TAG, MPI_COMM_WORLD);
                    globalResult = l_False;
                    for(int i = 0 ; i < nbThreads ; i++)
                        solvers[i].interrupt();
                }
                break;
            case NEW_FREE_SLAVE_TAG:
                master_newFreeSlave(s);
                break;
            case STEAL_WORK_TAG:
                // Read this message:
                MPI_Recv(NULL, 0, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
                for(int i = 0 ; i < nbThreads ; i++)
                    stealRequestPending[i] = true;
                break;
            default:
                assert(false && "UNKNOWN MESSAGE TYPE!!!");
            }
        }
        else{
            communication_done = true;
        }
    }

    return status;
}

bool Cooperation::rejectByBIG(Lit l1, Lit l2){
    // TODO
    return false;
}

void Cooperation::storeInBIG(Lit l1, Lit l2){
    // TODO
}
/*
   *  Run by communication thread
   * */
void Cooperation::handleReceivedClauses(int * recvData, int length){
    // Just copy the clauses to the shared memory buffers!
    int index = 0;
    int cnt = 0;
    // First read unit clauses:
    int numUnits = recvData[0];

    for(index=1 ; index <= numUnits ; index++){
        handleNewUnit(toLit(recvData[index]), false);

    }
    // Read other clauses
    assert(index == numUnits+1);
    while(index < length){
        numClausesReceived++;
        int size = recvData[index++];
        int lbd = recvData[index++];
        vec<Lit> ps;
        for(int i = 0 ; i < size ; i++){
            assert(index < length);
            ps.push(toLit(recvData[index++]));
        }

        bool send = true;
        if(ps.size() == 2){
            if(rejectByBIG(ps[0], ps[1])){
                // TODO: Store that this was rejected!
                send = false;
            }
        }
        if(send)
            exportExtraClause(nbThreads, ps, lbd, nbThreads, 0);
        cnt++;
    }
    assert(index == length);
}
/**************************
   * Store a clause in the MPI buffer.
   * NOTE: The header contains 4 integers for size, lbd, id of learning thread, and index!
   * */
void Cooperation::storeClauseInMPIBuffer(Lit * l){
    if(!useMPI)
        return;

    int size = var(l[0]);
    int lbd = var(l[1]);
    MPI_out_queue_clauses.push_back(std::vector<int>());
    std::vector<int> & toFill = MPI_out_queue_clauses.back();
    toFill.push_back(size);
    toFill.push_back(lbd);
    for(int i = 0 ; i < size ; i++)
        toFill.push_back(toInt(l[i+4]));
}

void Cooperation::clauseDeleted(int sender, int origin, int index){
    if(exportPolicy != EXPORT_LAZY_EXCHANGE)
        return;
    int ind = tailDeletedMessages[sender];
    if((ind + 2) % USAGE_BUFFER_SIZE == headDeletedMessages[sender]){
        printf("c sending deleted message: buffer is full (sender=%d)! \n", sender);
    }
    else{
        deletedMessages[sender][ind] = origin;
        deletedMessages[sender][ind+1] = index;
    }
    ind+=2;
    if(ind == USAGE_BUFFER_SIZE)
        ind = 0;
    tailDeletedMessages[sender] = ind;
    
}
void Cooperation::clauseUsed(int sender, int origin, int index){
    if(exportPolicy != EXPORT_LAZY_EXCHANGE)
        return;
    int ind = tailUsedMessages[sender];
    if((ind + 2) % USAGE_BUFFER_SIZE == headUsedMessages[sender]){
        printf("c sending used message: buffer is full (sender=%d)! \n", sender);
    }
    else{
        usedMessages[sender][ind] = origin;
        usedMessages[sender][ind+1] = index;
    }
    ind+=2;
    if(ind == USAGE_BUFFER_SIZE)
        ind = 0;
    tailUsedMessages[sender] = ind;
    
}

int Cooperation::clauseUsed(int origin, int index){
    int rVal = 0;
    std::pair<int, int> key(origin, index);
    std::map<std::pair<int, int>, std::vector<int> >::iterator it = lazyClauseStorage.find(key);
    if(it != lazyClauseStorage.end()){
        // Okay, export this clause:
        clausesUsed[key]++;
        if(clausesUsed[key] >= nbUsesBeforeSend){
            clausesUsed.erase(key);
            MPI_out_queue_clauses.push_back(std::vector<int>());
            std::vector<int> & tmp = MPI_out_queue_clauses.back();
            int size = it->second[0];
            assert(size + SIZE_CLAUSE_HEADER == it->second.size());
            assert(it->second[2] == origin);
            assert(it->second[3] == index);
            tmp.push_back(it->second.size() - SIZE_CLAUSE_HEADER); // The size
            tmp.push_back(it->second[1]); // The LBD
            for(int i = 0 ; i < size ; i++)
                tmp.push_back(it->second[i + SIZE_CLAUSE_HEADER]);
            lazyClauseStorage.erase(it);
            rVal = 1;
        }
    }
    return rVal;
}

int Cooperation::readUsageBuffers(){
    int rVal = 0;
    assert(exportPolicy == EXPORT_LAZY_EXCHANGE);
    for(int i = 0 ; i < nbBuffers ; i++){
        int head = headUsedMessages[i];
        int tail = tailUsedMessages[i];
        //printf("c buffer %d: head=%d ,tail=%d\n", i, headUsedMessages[i], tailUsedMessages[i]);
        if(head == tail)
            continue;
        int end = tail;
        if(tail < head)
            end = USAGE_BUFFER_SIZE;
        for(int j = head ; j < end ; j+=2){
            int origin = usedMessages[i][j];
            int index = usedMessages[i][j+1];
            clausesUsed[std::make_pair(origin, index)]++;
            rVal += clauseUsed(origin, index);
        }
        if(tail < head){
            for(int j = 0 ; j < tail ; j+=2){
                int origin = usedMessages[i][j];
                int index = usedMessages[i][j+1];
                clausesUsed[std::make_pair(origin, index)]++;
                rVal += clauseUsed(origin, index);
            }
        }
        head = tail;
        if(head == USAGE_BUFFER_SIZE)
            head = 0;
        headUsedMessages[i] = head;
    }
    return rVal;
}

void Cooperation::readDeletedBuffers(){
    for(int i = 0 ; i < nbBuffers ; i++){
        int head = headDeletedMessages[i];
        int tail = tailDeletedMessages[i];
        if(head == tail)
            continue;
        int end = tail;
        if(tail < head)
            end = USAGE_BUFFER_SIZE;
        for(int j = head ; j < end ; j+=2){
            int origin = deletedMessages[i][j];
            int index = deletedMessages[i][j+1];
            clausesDeleted[std::make_pair(origin, index)]++;
        }
        if(tail < head){
            for(int j = 0 ; j < tail ; j+=2){
                int origin = deletedMessages[i][j];
                int index = deletedMessages[i][j+1];
                clausesDeleted[std::make_pair(origin, index)]++;
            }
        }
        head = tail;
        if(head == USAGE_BUFFER_SIZE)
            head = 0;
        headDeletedMessages[i] = head;
    }
}

void Cooperation::printUsageStats(){
    int numUsed[nbThreads];
    int numDeleted[nbThreads];
    for(int i = 0 ; i < nbThreads ; i++){
        numUsed[i] = numDeleted[i] = 0;
    }
    for(std::map<std::pair<int, int>, int>::iterator it = clausesDeleted.begin() ; it != clausesDeleted.end();it++){
        if(it->second > nbThreads){
            printf("c wtf? deleted %d times! \n", it->second);
        }
        else{
            numDeleted[it->second]++;
        }
    }
    for(std::map<std::pair<int, int>, int>::iterator it = clausesUsed.begin() ; it != clausesUsed.end();it++){
        if(it->second > nbThreads){
            printf("c wtf? deleted %d times! \n", it->second);
        }
        else{
            numUsed[it->second]++;
        }
    }
    
    printf("c deleted: ");
    for(int i = 0 ; i < nbThreads ; i++)
        printf("%d ", numDeleted[i]);
    printf("\n");
    printf("c used: ");
    for(int i = 0 ; i < nbThreads ; i++)
        printf("%d ", numUsed[i]);
    printf("\n");
}

/*
   * Read messages from solver threads, and form messages for MPI
   * */
void Cooperation::readCubeConquerBuffers(){
    pthread_mutex_lock(& cube_lock);
    if(notificationFailedCubes.size() > 0){
        for(int i = 0 ; i < notificationFailedCubes.size();i++){
            std::pair<int, int> & msg = notificationFailedCubes[i];
            printf("c sending message to master: cube of size %d failed (threadIndex %d)\n", msg.second, msg.first);
            int buffer[2];
            buffer[0] = msg.first;
            buffer[1] = msg.second;
            send_wrapper(buffer, 2, MPI_INT, 0, CUBE_FAILED_TAG, MPI_COMM_WORLD);
            // Update solver state:
            solverStates[msg.first] = SOLVER_STATE_PORTFOLIO;
        }
        notificationFailedCubes.clear();
    }
    if(newCubesForMaster.size() > 0){
        printf("c communication received new cubes, sending them to master! \n");
        for(int i = 0 ; i < newCubesForMaster.size();i++){
            std::vector<int> & c = newCubesForMaster[i];
            int buffer[c.size()];
            printf("c cube ");
            for(int j = 0 ; j < c.size();j++){
                printf("%d ", c[j]);
                buffer[j] = c[j];
            }
            printf("\n");
            send_wrapper(buffer, (int) c.size(), MPI_INT, 0, NEW_CUBES_FOR_MASTER_TAG, MPI_COMM_WORLD);
            //buffer[c.size()-1]^=1;
            //MPI_Bsend(buffer, (int) c.size(), MPI_INT, 0, NEW_CUBES_FOR_MASTER_TAG, MPI_COMM_WORLD);

        }
        newCubesForMaster.clear();
    }
    if(newFreeSlaves.size() > 0){
        int buffer[newFreeSlaves.size()];
        for(int i = 0 ; i < newFreeSlaves.size();i++)
            buffer[i] = newFreeSlaves[i];
        send_wrapper(buffer, (int) newFreeSlaves.size(), MPI_INT, 0, NEW_FREE_SLAVE_TAG, MPI_COMM_WORLD);
        newFreeSlaves.clear();
    }
    pthread_mutex_unlock(& cube_lock);
}

void Cooperation::master_organize_cnc(double & time_last_steal){
    if(procId == 0){
        // Are there open jobs, and free slaves?
        if(master_OpenJobs.size() == 0 && MPI_Wtime() > time_last_steal + 5){
            printf("c time is %lf, sending steal requests! \n", MPI_Wtime());
            time_last_steal = MPI_Wtime();
            for(int i = 0 ; i < numProcesses ; i++){
                send_wrapper(NULL, 0, MPI_INT, i, STEAL_WORK_TAG, MPI_COMM_WORLD);
            }
        }
        while(master_OpenJobs.size() > 0 && freeSlaves.size() > 1){
            int nextSlave = freeSlaves.front();
            freeSlaves.pop_front();
            assert(solverStates[nextSlave] = SOLVER_STATE_PORTFOLIO);
            std::vector<int> & nextCube = master_OpenJobs.front();
            int arr[nextCube.size()+1];
            arr[0] = nextSlave;
            for(int i = 0 ; i < nextCube.size();i++)
                arr[i+1] = nextCube[i];
            int procId = getProcId(nextSlave);
            send_wrapper(arr, nextCube.size()+1, MPI_INT, procId, NEW_CUBE_FOR_SLAVE_TAG, MPI_COMM_WORLD);

            master_OpenJobs.pop_front();
            solverStates[nextSlave] = SOLVER_STATE_CNC;
        }
    }
}
void Cooperation::master_receive_new_cubes(MPI_Status & s){
    int length;
    MPI_Get_count(&s, MPI_INT, &length);
    int arr[length];
    MPI_Recv(arr, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
    std::vector<int> newCube;
    for(int i = 0 ; i < length ; i++)
        newCube.push_back(arr[i]);
    master_OpenJobs.push_back(newCube);
    
}
/*
   * Returns true if the problem has been solved, and false otherwise
   * */
bool Cooperation::master_receive_failed_cube(MPI_Status & s){
    int length;
    assert(0 == procId);
    MPI_Get_count(&s, MPI_INT, &length);
    assert(length == 2);
    int arr[length];
    MPI_Recv(arr, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
    printf("c master received message about failed cube: %d %d\n", arr[0], arr[1]);
    int cubeLength = arr[1];
    if(length == 0){
        printf("c got UNSAT quickly??? \n");
    }
    while(progress.size() <= cubeLength)
        progress.push_back(0);
    while(progress[cubeLength] == 1)
        progress[cubeLength--]=0;
    progress[cubeLength]=1;
    printf("c progress: ");
    for(int i = 0 ; i < progress.size();i++)
        printf("%d ", progress[i]);
    printf("\n");
    return progress[0]==1;
}

void Cooperation::comForwardCubes(MPI_Status & s){
    assert(s.MPI_TAG == NEW_CUBE_FOR_SLAVE_TAG);
    
    int length;
    MPI_Get_count(&s, MPI_INT, &length);
    int arr[length];
    MPI_Recv(arr, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
    int threadIndex = arr[0];
    printf("c received cube for thread %d, state there is %d\n", threadIndex, solverStates[threadIndex]);
    assert(procId == 0 ||  solverStates[threadIndex] == SOLVER_STATE_PORTFOLIO);
    assert(getProcId(threadIndex) == procId);
    pthread_mutex_lock(&cube_lock);
    int localId = getLocalThreadId(threadIndex);
    assert(newCubesForSlave[localId].size() == 0);
    for(int i = 1 ; i < length ; i++)
        newCubesForSlave[localId].push_back(arr[i]);
    cubePending[localId] = true;
    pthread_mutex_unlock(&cube_lock);
}
void Cooperation::master_newFreeSlave(MPI_Status & s){
    assert(s.MPI_TAG == NEW_FREE_SLAVE_TAG);
    assert(procId == 0);
    
    int length;
    MPI_Get_count(&s, MPI_INT, &length);
    int newFreeIndex[length];
    
    MPI_Recv(newFreeIndex, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
    for(int i = 0 ; i < length ; i++){
        assert(procId == 0 ||  solverStates[newFreeIndex[i]] == SOLVER_STATE_CNC);
        solverStates[newFreeIndex[i]] = SOLVER_STATE_PORTFOLIO;
        freeSlaves.push_back(newFreeIndex[i]);
        printf("c new free slave: %d now have %lu open jobs and %lu free slaves \n", newFreeIndex[i], master_OpenJobs.size(), freeSlaves.size());
    }
}

void Cooperation::send_wrapper(void * data, int num, MPI_Datatype d, int dest, int tag, MPI_Comm c){
    int size = 0;
    MPI_Type_size(d, &size);
    numMessagesSent++;
    numBytesSent += num*size;
    MPI_Bsend(data, num, d, dest, tag, c);
}

void Cooperation::adjustNumThreads               (int maxThreads, int maxMem){
    double memUsedNow = memUsed();
    int maxNum = (0.5 * (double)maxMem / memUsedNow);
    printf("c adjusting to %d solvers (0.5 * %d / %lf)\n", maxNum, maxMem, memUsedNow);
    printf("c solver guesses mem usage of %lf\n", solvers[0].estimateMemUsage());
    if(maxNum > maxThreads)
        maxNum = maxThreads;
    if(maxNum < 1)
        maxNum = 1;
    nbThreads = maxNum;
    nbBuffers = nbThreads+1;
}
}
