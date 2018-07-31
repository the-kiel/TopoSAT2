/***************************************************************************************[Solver.cc]
 * Glucose -- Copyright (c) 2013, Gilles Audemard, Laurent Simon
 *				CRIL - Univ. Artois, France
 *				LRI  - Univ. Paris Sud, France
 *
 * Glucose sources are based on MiniSat (see below MiniSat copyrights). Permissions and copyrights of
 * Glucose are exactly the same as Minisat on which it is based on. (see below).
 *
 * ---------------
 *
 * Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
 * Copyright (c) 2007-2010, Niklas Sorensson
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
 **************************************************************************************************/

#include <math.h>

#include "mtl/Sort.h"
#include "core/Solver.h"
#include "core/Constants.h"
#include "utils/System.h"

#include "core/Cooperation.h"
#include "Determanager.h"
using namespace Glucose;

//=================================================================================================
// Options:

static const char* _cat = "CORE";
static const char* _cr = "CORE -- RESTART";
static const char* _cred = "CORE -- REDUCE";
static const char* _cm = "CORE -- MINIMIZE";
static const char* _certified = "CORE -- CERTIFIED UNSAT";

static const char* _cp = "CORE -- PARALLEL";


static DoubleOption  opt_step_size         (_cat, "step-size",   "Initial step size",                             0.40,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_step_size_dec     (_cat, "step-size-dec","Step size decrement",                          0.000001, DoubleRange(0, false, 1, false));
static DoubleOption  opt_min_step_size     (_cat, "min-step-size","Minimal step size",                            0.06,     DoubleRange(0, false, 1, false));
static BoolOption    opt_VSIDS      (_cat, "vsids",    "use VSIDS", true);

static BoolOption opt_incremental (_cat,"incremental", "Use incremental SAT solving",false);
static DoubleOption opt_K                 (_cr, "K",           "The constant used to force restart",            0.8,     DoubleRange(0, false, 1, false));
static DoubleOption opt_R                 (_cr, "R",           "The constant used to block restart",            1.4,     DoubleRange(1, false, 5, false));
static IntOption     opt_size_lbd_queue     (_cr, "szLBDQueue",      "The size of moving average for LBD (restarts)", 50, IntRange(10, INT32_MAX));
static IntOption     opt_size_trail_queue     (_cr, "szTrailQueue",      "The size of moving average for trail (block restarts)", 5000, IntRange(10, INT32_MAX));

static IntOption     opt_first_reduce_db     (_cred, "firstReduceDB",      "The number of conflicts before the first reduce DB", 2000, IntRange(0, INT32_MAX));
static IntOption     opt_inc_reduce_db     (_cred, "incReduceDB",      "Increment for reduce DB", 300, IntRange(0, INT32_MAX));
static IntOption     opt_spec_inc_reduce_db     (_cred, "specialIncReduceDB",      "Special increment for reduce DB", 1000, IntRange(0, INT32_MAX));
static IntOption    opt_lb_lbd_frozen_clause      (_cred, "minLBDFrozenClause",        "Protect clauses if their LBD decrease and is lower than (for one turn)", 30, IntRange(0, INT32_MAX));

static IntOption     opt_lb_size_minimzing_clause     (_cm, "minSizeMinimizingClause",      "The min size required to minimize clause", 30, IntRange(3, INT32_MAX));
static IntOption     opt_lb_lbd_minimzing_clause     (_cm, "minLBDMinimizingClause",      "The min LBD required to minimize clause", 6, IntRange(3, INT32_MAX));
static IntOption     opt_delayBeforeCheck     (_cm, "delayBeforeCheck",      "The number of conflicts before trying to reduce a clause", 100, IntRange(0, INT32_MAX));

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.8,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);


static BoolOption    opt_lowLLevelClauseImport      (_cp, "lowLevelImport",    "Import clauses when solver seems to be close the the root", true);
static BoolOption    opt_restartPortfolio      (_cp, "restartPortfolio",    "Use different restart strategies", false);
static BoolOption    opt_clauseImportBetweenRestarts      (_cp, "intermediateImport",    "import clauses between restarts", true);
static BoolOption    opt_chanseOk     (_cp, "chanseOk",    "Use chanseOk-style clause DB management", true);


static BoolOption    opt_subSimpCheck     (_cp, "subSimpCheck",    "Use check for self-subsuming resolution on one core", false);
static BoolOption    opt_FullubSimpCheck     (_cp, "fullSubSimpCheck",    "Use full check for self-subsuming resolution on one core", false);
static BoolOption    opt_PromoteOneWatched     (_cp, "promote1wtch",    "Promote one-watched clauses after restarts", false);
static BoolOption    opt_hashTest     (_cp, "hashTest",    "Regularly hash all clauses from the permanent database and check for duplicates", false);


static IntOption     opt_protect_receiveds      (_cp, "protectRecvFor", "Protect received clauses for this number of conflicts", 30000, IntRange(0, INT32_MAX));

static IntOption     opt_protect_learnts      (_cp, "protectLocalFor", "Protect learnt clauses with LBD <= 6 for this number of conflicts", 30000, IntRange(0, INT32_MAX));
static IntOption     opt_threshold_permanent      (_cp, "thresholdPermanent", "permanently protect clauses if their LBD is lower or equal to this value", 3, IntRange(0, 32));
static IntOption     opt_threshold_mediumLBD      (_cp, "thresholdMedium", "Keep clauses in medium lbd storage if their LBD is less or equal to this value", 6, IntRange(0, 32));

static IntOption     opt_maxActSize      (_cp, "maxActSize", "Maximum size of DB for clauses which are kept due to their activity", 50000, IntRange(500, INT32_MAX));
static IntOption     opt_reduceInterval      (_cp, "reduceInterval", "Interval between two reductions of the LBD-based clause database", 15000, IntRange(500, INT32_MAX));

/*
 * static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
 * static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
 */
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));


BoolOption    opt_certified      (_certified, "certified",    "Certified UNSAT using DRUP format", false);
StringOption    opt_certified_file      (_certified, "certified-output",    "Certified UNSAT output file", "NULL");


//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
  , showModel        (0)
  , K              (opt_K)
  , R              (opt_R)
  , sizeLBDQueue   (opt_size_lbd_queue)
  , sizeTrailQueue   (opt_size_trail_queue)
  , firstReduceDB  (opt_first_reduce_db)
  , incReduceDB    (opt_inc_reduce_db)
  , specialIncReduceDB    (opt_spec_inc_reduce_db)
  , lbLBDFrozenClause (opt_lb_lbd_frozen_clause)
  , lbSizeMinimizingClause (opt_lb_size_minimzing_clause)
  , lbLBDMinimizingClause (opt_lb_lbd_minimzing_clause)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , certifiedOutput  (NULL)
  , certifiedUNSAT   (opt_certified)
  , useVSIDS(opt_VSIDS)
  , step_size        (opt_step_size)
  , step_size_dec    (opt_step_size_dec)
  , min_step_size    (opt_min_step_size)
  // Statistics: (formerly in 'SolverStats')
  //
  ,  nbRemovedClauses(0),nbReducedClauses(0), nbDL2(0),nbBin(0),nbUn(0) , nbReduceDB(0)
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0),propagations_lift(0), conflicts(0),conflictsRestarts(0),nbstopsrestarts(0),nbstopsrestartssame(0),lastblockatrestart(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
  , sumOfReductionTimes(0.0)
  , curRestart(1)
  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches            (WatcherDeleted(ca))
  , watchesBin            (WatcherDeleted(ca))
  , unaryWatches        (unaryWatchRemoved(ca))
  , use_chanseok_style(opt_chanseOk)
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (VarOrderLt(activity))
  , progress_estimate  (0)
  , remove_satisfied   (true)
  , conflicts_next_reduce(opt_reduceInterval)
  , conflicts_reduce_interval(opt_reduceInterval)
  , maxActivitySize(opt_maxActSize)
  // Resource constraints:
  //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
  , incremental(opt_incremental)
  , nbVarsInitialFormula(INT32_MAX)

{
    MYFLAG=0;
    // Initialize only first time. Useful for incremental solving, useless otherwise
    lbdQueue.initSize(sizeLBDQueue);
    trailQueue.initSize(sizeTrailQueue);
    sumLBD = 0;
    
    nbclausesbeforereduce = firstReduceDB;
    totalTime4Sat=0;totalTime4Unsat=0;
    nbSatCalls=0;nbUnsatCalls=0;
    
    
    if(certifiedUNSAT) {
        if(!strcmp(opt_certified_file,"NULL")) {
            certifiedOutput =  fopen("/dev/stdout", "wb");
        } else {
            certifiedOutput =  fopen(opt_certified_file, "wb");
        }
        //    fprintf(certifiedOutput,"o proof DRUP\n");
    }
}


Solver::~Solver()
{
}


/****************************************************************
 * Set the incremental mode
 ****************************************************************/

// This function set the incremental mode to true.
// You can add special code for this mode here.

void Solver::setIncrementalMode() {
    incremental = true;
}

// Number of variables without selectors
void Solver::initNbInitialVars(int nb) {
    nbVarsInitialFormula = nb;
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    watchesBin  .init(mkLit(v, false));
    watchesBin  .init(mkLit(v, true ));
    unaryWatches.init(mkLit(v, false));
    unaryWatches.init(mkLit(v, true));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    //activity .push(0);
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    permDiff  .push(0);
    permDiff  .push(0); // For both polarities, so it can also be used for literals.
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    picked.push(0);
    conflicted.push(0);
    almost_conflicted.push(0);
    return v;
}



bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;
    
    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    
    vec<Lit>    oc;
    oc.clear();
    
    Lit p; int i, j, flag = 0;
    if(certifiedUNSAT) {
        for (i = j = 0, p = lit_Undef; i < ps.size(); i++) {
            oc.push(ps[i]);
            if (value(ps[i]) == l_True || ps[i] == ~p || value(ps[i]) == l_False)
                flag = 1;
        }
    }
    
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);
    
    if (flag && (certifiedUNSAT)) {
        for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
            fprintf(certifiedOutput, "%i ", (var(ps[i]) + 1) * (-2 * sign(ps[i]) + 1));
        fprintf(certifiedOutput, "0\n");
        
        fprintf(certifiedOutput, "d ");
        for (i = j = 0, p = lit_Undef; i < oc.size(); i++)
            fprintf(certifiedOutput, "%i ", (var(oc[i]) + 1) * (-2 * sign(oc[i]) + 1));
        fprintf(certifiedOutput, "0\n");
    }
    
    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }
    
    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    
    assert(c.size() > 1);
    if(c.size()==2) {
        watchesBin[~c[0]].push(Watcher(cr, c[1]));
        watchesBin[~c[1]].push(Watcher(cr, c[0]));
    } else {
        watches[~c[0]].push(Watcher(cr, c[1]));
        watches[~c[1]].push(Watcher(cr, c[0]));
    }
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver::attachClausePurgatory(CRef cr) {
    const Clause& c = ca[cr];

    assert(c.size() > 1);
    unaryWatches[~c[0]].push(Watcher(cr, c[1]));

}

void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];

    assert(c.size() > 1);
    if(c.size()==2) {
        if (strict){
            remove(watchesBin[~c[0]], Watcher(cr, c[1]));
            remove(watchesBin[~c[1]], Watcher(cr, c[0]));
        }else{
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watchesBin.smudge(~c[0]);
            watchesBin.smudge(~c[1]);
        }
    } else {
        if (strict){
            remove(watches[~c[0]], Watcher(cr, c[1]));
            remove(watches[~c[1]], Watcher(cr, c[0]));
        }else{
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watches.smudge(~c[0]);
            watches.smudge(~c[1]);
        }
    }
    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }

void Solver::detachClausePurgatory(CRef cr, bool strict) {
    const Clause& c = ca[cr];

    assert(c.size() > 1);
    if (strict)
        remove(unaryWatches[~c[0]], Watcher(cr, c[1]));
    else
        unaryWatches.smudge(~c[0]);
}


void Solver::removeClause(CRef cr) {

    Clause& c = ca[cr];

    if (certifiedUNSAT) {
        fprintf(certifiedOutput, "d ");
        for (int i = 0; i < c.size(); i++)
            fprintf(certifiedOutput, "%i ", (var(c[i]) + 1) * (-2 * sign(c[i]) + 1));
        fprintf(certifiedOutput, "0\n");
    }
    if(c.isOneWatched())
        detachClausePurgatory(cr);
    else
        detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1);
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    if(incremental)  // Check clauses with many selectors is too time consuming
        return (value(c[0]) == l_True) || (value(c[1]) == l_True);

    // Default mode.
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false;
}

/************************************************************
         * Compute LBD functions
         *************************************************************/

inline unsigned int Solver::computeLBD(const vec<Lit> & lits,int end) {
    int nblevels = 0;
    MYFLAG++;

    if(incremental) { // ----------------- INCREMENTAL MODE
        if(end==-1) end = lits.size();
        unsigned int nbDone = 0;
        for(int i=0;i<lits.size();i++) {
            if(nbDone>=end) break;
            if(isSelector(var(lits[i]))) continue;
            nbDone++;
            int l = level(var(lits[i]));
            if (permDiff[l] != MYFLAG) {
                permDiff[l] = MYFLAG;
                nblevels++;
            }
        }
    } else { // -------- DEFAULT MODE. NOT A LOT OF DIFFERENCES... BUT EASIER TO READ
        for(int i=0;i<lits.size();i++) {
            int l = level(var(lits[i]));
            if (permDiff[l] != MYFLAG) {
                permDiff[l] = MYFLAG;
                nblevels++;
            }
        }
    }

    return nblevels;
}

inline unsigned int Solver::computeLBD(const Clause &c) {
    int nblevels = 0;
    MYFLAG++;

    if(incremental) { // ----------------- INCREMENTAL MODE
        int nbDone = 0;
        for(int i=0;i<c.size();i++) {
            if(nbDone>=c.sizeWithoutSelectors()) break;
            if(isSelector(var(c[i]))) continue;
            nbDone++;
            int l = level(var(c[i]));
            if (permDiff[l] != MYFLAG) {
                permDiff[l] = MYFLAG;
                nblevels++;
            }
        }
    } else { // -------- DEFAULT MODE. NOT A LOT OF DIFFERENCES... BUT EASIER TO READ
        for(int i=0;i<c.size();i++) {
            int l = level(var(c[i]));
            if (permDiff[l] != MYFLAG) {
                permDiff[l] = MYFLAG;
                nblevels++;
            }
        }
    }
    return nblevels;
}


/******************************************************************
         * Minimisation with binary reolution
         ******************************************************************/
void Solver::minimisationWithBinaryResolution(vec<Lit> &out_learnt) {

    // Find the LBD measure
    unsigned int lbd = computeLBD(out_learnt);
    Lit p = ~out_learnt[0];

    if(lbd<=lbLBDMinimizingClause){
        MYFLAG++;

        for(int i = 1;i<out_learnt.size();i++) {
            permDiff[var(out_learnt[i])] = MYFLAG;
        }

        vec<Watcher>&  wbin  = watchesBin[p];
        int nb = 0;
        for(int k = 0;k<wbin.size();k++) {
            Lit imp = wbin[k].blocker;
            if(permDiff[var(imp)]==MYFLAG && value(imp)==l_True) {
                nb++;
                permDiff[var(imp)]= MYFLAG-1;
            }
        }
        int l = out_learnt.size()-1;
        if(nb>0) {
            nbReducedClauses++;
            for(int i = 1;i<out_learnt.size()-nb;i++) {
                if(permDiff[var(out_learnt[i])]!=MYFLAG) {
                    Lit p = out_learnt[l];
                    out_learnt[l] = out_learnt[i];
                    out_learnt[i] = p;
                    l--;i--;
                }
            }

            out_learnt.shrink(nb);

        }
    }
}

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            if (phase_saving > 1 || ((phase_saving == 1) && c > trail_lim.last()))
                polarity[x] = sign(trail[c]);
            insertVarOrder(x);
            if(!useVSIDS){
                int age = conflicts - picked[x];
                if(age > 0){

                    double adjusted_reward = ((double) (conflicted[x] + almost_conflicted[x])) / ((double) age);
                    double old_activity = activity[x];
                    activity[x] = step_size * adjusted_reward + ((1 - step_size) * old_activity);
                    assert(!useVSIDS);
                    // This may happen when using LRB and importing clauses during search, as the conflict counter is not incremented there.
                    // TODO
                    if(conflicted[x]+almost_conflicted[x] > age){
                        //printf("c wtf? x=%d conflicted[x]=%d almost_conflicted[x]=%d  age=%d reward %lf newAct %lf old act %lf conflicts %d picked[x]=%d \n", x, conflicted[x],almost_conflicted[x], age, adjusted_reward, activity[x], old_activity, conflicts, picked[x]);
                        //                             getchar();
                    }
                    if (order_heap.inHeap(x)){
                        if (activity[x] > old_activity)
                            order_heap.decrease(x);
                        else
                            order_heap.increase(x);
                    }
                }
            }

        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    }
}


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}
/*
         *  Find the set of decision literals which
         *  - causes this conflict (if there was one)
         *  - caused this clause to propagate (in case one of the literals from this clause was propagated to "true" by exactly this clause
         * */
void Solver::useSimpleAnalyse(CRef confl, vec<Lit> & out_learnt, bool clauseWasTrue){
    MYFLAG++;
    int pathC = 0;
    int index = trail.size() - 1;
    assert(confl != CRef_Undef);
    Clause & c = ca[confl];
    bool debug = false;
    if(debug) printf("c useSimpleAnalyse called. wasTrue: %d Clause in conflict: ", clauseWasTrue);
    for(int i = 0 ; i < c.size();i++){
        Lit p = c[i];
        if(level(var(p)) > 0){
            assert(permDiff[var(p)] != MYFLAG);
            assert(!seen[var(p)]);
            if(debug) printf("%d (=%c @ %d) ", showLit(c[i]), showVal(value(c[i])),  level(var(c[i])));
            seen[var(p)]=true;
            permDiff[var(p)] = MYFLAG;
            pathC++;
        }
    }
    if(debug) printf("\n");
    if(debug) printf("trail: ");

    while(pathC > 0){
        if(debug){
            for(int i = 0 ;i < 10 && i < trail.size() ; i++)
                printf("%d @ %d, %d \n", showLit(trail[i]), level(var(trail[i])), seen[var(trail[i])]);
        }
        if(debug) printf("new iteration with pathC = %d and index = %d\n", pathC, index);
        assert(index >= 0 && index <= trail.size() && "out of bounds");
        assert(var(trail[index]) >= 0 && "small var? ");
        assert(var(trail[index]) < seen.size() && "Huge var? ");
        if(debug) printf("index %d \n", index);
        if(debug) printf("var %d \n", var(trail[index]));
        if(debug) printf("seen.size()=%d\n", seen.size());
        while(!seen[var(trail[index])]){
            if(debug) printf("now index=%d \n", index);
            assert(index > 0 && "index becomes too small in loop! ");
            index--;
        }
        if(debug) printf("now index=%d\n", index);
        assert(index+1 >= 0 && "out of range for trail access! ");
        assert(index < trail.size());
        Lit p = trail[index];
        if(debug) printf("\n next: var %d \n", var(p)+1);
        assert(level(var(p)) > 0 && "No root level variables! ");
        assert(seen[var(p)]);
        assert(permDiff[var(p)] = MYFLAG);
        confl = reason(var(p));
        if(debug) printf("reason for %d : ", showLit(p));
        if(confl == CRef_Undef){
            out_learnt.push(~p);
            seen[var(p)] = false;
            if(debug) printf(" UNDEF \n");
            pathC--;
        }
        else{
            Clause & c = ca[confl];
            for(int i = 0 ; i < c.size() ; i++){
                if(debug) printf("%d (=%c@%d, seen %d ) ", showLit(c[i]), showVal(value(c[i])),  level(var(c[i])), seen[var(c[i])]);
                if(!seen[var(c[i])] && level(var(c[i])) > 0){
                    if(value(c[i]) == l_True){
                        if(debug) printf(" (now it would crash if I dont prevent it..) ");
                        assert(permDiff[var(c[i])] == MYFLAG);
                    }
                    else {
                        assert(permDiff[var(c[i])] != MYFLAG);
                        seen[var(c[i])] = true;
                        pathC++;
                        permDiff[var(c[i])] = MYFLAG;
                    }
                }
            }
            if(debug) printf("\n");
            seen[var(p)] = false;
            pathC--;
        }
        //                 printf("c now pathC=%d\n", pathC);
    }
    //             printf("and done! \n");
    // Old version
    /*
            int pathC = 0;
            for(int i = 0 ; i < seen.size();i++)
                assert(!seen[i]);
            printf("c useSimpleAnalyse called. Clause in conflict: ");
            vec<Lit> indices_to_clear;
            assert(confl != CRef_Undef);
            Clause & c = ca[confl];
            for(int i = 0 ; i < c.size();i++){
                if(level(var(c[i])) > 0){
                    if(!clauseWasTrue)
                        assert(value(c[i]) == l_False);
                    seen[var(c[i])]=1;
                    indices_to_clear.push(c[i]);
                    pathC++;
                    printf("%d (@ %d) ", showLit(c[i]), level(var(c[i])));
                }
            }
            printf("\n");
            
            int index = trail.size() - 1;
            while(pathC > 0){
                while(!seen[var(trail[index])]) {
                    index--;
                    if(index < 0 || level(var(trail[index])) == 0){
                        printf("c this is bad. out_learnt.size() = %d, pathC = %d, index = %d, DL %d\n", out_learnt.size(), pathC, index, decisionLevel());
                    }
                    assert(index >= 0);
                }
                Lit p = trail[index];
                confl = reason(var(p));
                printf("reason for %d : ", showLit(p));
                if(confl == CRef_Undef){
                    printf(" UNDEF \n");
                    out_learnt.push(~p);
                    pathC--;
                    indices_to_clear.push(p);
                }
                else{
                    Clause & c = ca[confl];
                    for(int i = 0 ; i < c.size();i++){
                        printf("%d (@%d, seen %d ) ", showLit(c[i]), level(var(c[i])), seen[var(c[i])]);
                        if(!seen[var(c[i])] && level(var(c[i])) > 0){
                            seen[var(c[i])]=true;
                            indices_to_clear.push(c[i]);
                            pathC++;
                        }
                    }
                    printf("\n");
                    indices_to_clear.push(p);
                    pathC--;
                }
                index--;
            }
            printf("c have %d indices to clear, out.size()=%d \n", indices_to_clear.size(), out_learnt.size());
            for(int i  = 0 ; i < indices_to_clear.size();i++)
                seen[var(indices_to_clear[i])]=false;
            for(int i = 0 ; i < seen.size();i++)
                assert(!seen[i]);
            */
}

/*_________________________________________________________________________________________________
         * |
         * |  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
         * |
         * |  Description:
         * |    Analyze conflict and produce a reason clause.
         * |
         * |    Pre-conditions:
         * |      * 'out_learnt' is assumed to be cleared.
         * |      * Current decision level must be greater than root level.
         * |
         * |    Post-conditions:
         * |      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
         * |      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
         * |        rest of literals. There may be others from the same level though.
         * |
         * |________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt,vec<Lit>&selectors, int& out_btlevel,unsigned int &lbd,unsigned int &szWithoutSelectors)
{
    int pathC = 0;
    Lit p     = lit_Undef;
    //std::set<Var> vars_bumped;
    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        // Special case for binary clauses
        // The first one has to be SAT
        if( p != lit_Undef && c.size()==2 && value(c[0])==l_False) {

            assert(value(c[1])==l_True);
            Lit tmp = c[0];
            c[0] =  c[1], c[1] = tmp;
        }

        if(c.isReceived() && !c.wasUsed()){

            coop->clauseUsed(threadId, c.getOrigin(), c.getIndex());
            //printf("c clause used: size %d age %d\n", c.size(), conflicts - c.getLastTouched());
        }
        c.setUsed(true);
        if (c.learnt()){
            claBumpActivity(c);
            c.setLastTouched(conflicts);
        }

#ifdef DYNAMICNBLEVEL
        // DYNAMIC NBLEVEL trick (see competition'09 companion paper)
        if(c.learnt()  && c.lbd()>2) {
            unsigned int nblevels = computeLBD(c);
            if(nblevels+1<c.lbd() ) { // improve the LBD
                if(c.lbd()<=lbLBDFrozenClause) {
                    c.setCanBeDel(false);
                }
                // seems to be interesting : keep it for the next round
                c.setLBD(nblevels); // Update it
            }
        }
#endif


        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                if(!isSelector(var(q))){
                    if(useVSIDS)
                        varBumpActivity(var(q));
                    else
                        conflicted[var(q)]++;
                    //vars_bumped.insert(var(q));
                }
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel()) {
                    pathC++;
#ifdef UPDATEVARACTIVITY
                    // UPDATEVARACTIVITY trick (see competition'09 companion paper)
                    if(!isSelector(var(q)) && (reason(var(q))!= CRef_Undef)  && ca[reason(var(q))].learnt())
                        lastDecisionLevel.push(q);
#endif

                } else {
                    if(isSelector(var(q))) {
                        assert(value(q) == l_False);
                        selectors.push(q);
                    } else
                        out_learnt.push(q);
                }
            }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;

    for(int i = 0;i<selectors.size();i++)
        out_learnt.push(selectors[i]);

    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];

    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                // Thanks to Siert Wieringa for this bug fix!
                for (int k = ((c.size()==2) ? 0:1); k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();


    /* ***************************************
             *      Minimisation with binary clauses of the asserting clause
             *      First of all : we look for small clauses
             *      Then, we reduce clauses with small LBD.
             *      Otherwise, this can be useless
             */
    if(!incremental && out_learnt.size()<=lbSizeMinimizingClause) {
        minimisationWithBinaryResolution(out_learnt);
    }
    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }


    // Compute the size of the clause without selectors (incremental mode)
    if(incremental) {
        szWithoutSelectors = 0;
        for(int i=0;i<out_learnt.size();i++) {
            if(!isSelector(var((out_learnt[i])))) szWithoutSelectors++;
            else if(i>0) break;
        }
    } else
        szWithoutSelectors = out_learnt.size();

    // Compute LBD
    lbd = computeLBD(out_learnt,out_learnt.size()-selectors.size());


#ifdef UPDATEVARACTIVITY
    // UPDATEVARACTIVITY trick (see competition'09 companion paper)
    if(useVSIDS && lastDecisionLevel.size()>0) {
        for(int i = 0;i<lastDecisionLevel.size();i++) {
            if(ca[reason(var(lastDecisionLevel[i]))].lbd()<lbd)
                varBumpActivity(var(lastDecisionLevel[i]));
        }
        lastDecisionLevel.clear();
    }
#endif

    if(!useVSIDS){
        if(p != lit_Undef){
            seen[var(p)]=true;
            analyze_toclear.push(p);
        }
        for(int i = out_learnt.size()-1 ; i >= 0 ; i--){
            Var v = var(out_learnt[i]);
            CRef rea = reason(v);
            if(rea != CRef_Undef){
                Clause & c_reason = ca[rea];
                for(int j = 0 ; j < c_reason.size();j++){
                    Lit l = c_reason[j];
                    if(!seen[var(l)]){
//                         if(vars_bumped.count(var(l))){
//                             printf("c okay, doubly dumping this stuff! length=%d lbd=%d \n", out_learnt.size(), lbd);
//                         }
                        seen[var(l)]=true;
                        analyze_toclear.push(l);
                        almost_conflicted[var(l)]++;
                    }
                }
            }
        }
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
    for(int j = 0 ; j<selectors.size() ; j++) seen[var(selectors[j])] = 0;
}





void Solver::analyze_vivification(CRef confl, vec<Lit>& out_learnt)
{
    int pathC = 0;
    Lit p     = lit_Undef;
    //std::set<Var> vars_bumped;
    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        // Special case for binary clauses
        // The first one has to be SAT
        if( p != lit_Undef && c.size()==2 && value(c[0])==l_False) {

            assert(value(c[1])==l_True);
            Lit tmp = c[0];
            c[0] =  c[1], c[1] = tmp;
        }


        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel()) {
                    pathC++;

                } else {
                    out_learnt.push(q);
                }
            }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;


    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];

    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                // Thanks to Siert Wieringa for this bug fix!
                for (int k = ((c.size()==2) ? 0:1); k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();


    /* ***************************************
             *      Minimisation with binary clauses of the asserting clause
             *      First of all : we look for small clauses
             *      Then, we reduce clauses with small LBD.
             *      Otherwise, this can be useless
             */
    minimisationWithBinaryResolution(out_learnt);


    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
    
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause& c = ca[reason(var(analyze_stack.last()))]; analyze_stack.pop();
        if(c.size()==2 && value(c[0])==l_False) {
            assert(value(c[1])==l_True);
            Lit tmp = c[0];
            c[0] =  c[1], c[1] = tmp;
        }

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
         * |
         * |  analyzeFinal : (p : Lit)  ->  [void]
         * |
         * |  Description:
         * |    Specialized analysis procedure to express the final conflict in terms of assumptions.
         * |    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
         * |    stores the result in 'out_conflict'.
         * |________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                //                for (int j = 1; j < c.size(); j++) Minisat (glucose 2.0) loop
                // Bug in case of assumptions due to special data structures for Binary.
                // Many thanks to Sam Bayless (sbayless@cs.ubc.ca) for discover this bug.
                for (int j = ((c.size()==2) ? 0:1); j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }

            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    if(!useVSIDS){
        Var v = var(p);
        conflicted[v] = almost_conflicted[v] = 0;
        picked[v] = conflicts;
    }
    trail.push_(p);
}


/*_________________________________________________________________________________________________
         * |
         * |  propagate : [void]  ->  [Clause*]
         * |
         * |  Description:
         * |    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
         * |    otherwise CRef_Undef.
         * |
         * |    Post-conditions:
         * |      * the propagation queue is empty, even if there was a conflict.
         * |________________________________________________________________________________________________@*/
CRef Solver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();
    watchesBin.cleanAll();
    unaryWatches.cleanAll();
    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;


        // First, Propagate binary clauses
        vec<Watcher>&  wbin  = watchesBin[p];

        for(int k = 0;k<wbin.size();k++) {

            Lit imp = wbin[k].blocker;

            if(value(imp) == l_False) {
                return wbin[k].cref;
            }

            if(value(imp) == l_Undef) {
                uncheckedEnqueue(imp,wbin[k].cref);
            }
        }



        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){

                *j++ = w; continue; }

            // Look for new watch:
            if(incremental) { // ----------------- INCREMENTAL MODE
                int choosenPos = -1;
                for (int k = 2; k < c.size(); k++) {

                    if (value(c[k]) != l_False){
                        if(decisionLevel()>assumptions.size()) {
                            choosenPos = k;
                            break;
                        } else {
                            choosenPos = k;

                            if(value(c[k])==l_True || !isSelector(var(c[k]))) {
                                break;
                            }
                        }

                    }
                }
                if(choosenPos!=-1) {
                    c[1] = c[choosenPos]; c[choosenPos] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }
            } else {  // ----------------- DEFAULT  MODE (NOT INCREMENTAL)
                for (int k = 2; k < c.size(); k++) {

                    if (value(c[k]) != l_False){
                        c[1] = c[k]; c[k] = false_lit;
                        watches[~c[1]].push(w);
                        goto NextClause; }
                }
            }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else {
                uncheckedEnqueue(first, cr);


            }
NextClause:;
        }
        ws.shrink(i - j);
        // TODO: Make this a parameter somewhere?

        bool useUnaryWatches = true;
        if(useUnaryWatches && confl == CRef_Undef){
            confl = propagateUnaryWatches(p);
            if(confl != CRef_Undef){
                //printf("c found conflict from unary watched clauses!!! \n");
                //Clause & c_test = ca[confl];
                //printf("c this clause has size %d and lbd (so far ;) %d\n", c_test.size(), c_test.lbd());
            }
        }
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}

CRef Solver::propagateUnaryWatches(Lit p) {
    CRef confl= CRef_Undef;
    Watcher *i, *j, *end;
    vec<Watcher>& ws = unaryWatches[p];
    for (i = j = (Watcher*) ws, end = i + ws.size(); i != end;) {
        // Try to avoid inspecting the clause:
        Lit blocker = i->blocker;
        if (value(blocker) == l_True) {
            *j++ = *i++;
            continue;
        }

        // Make sure the false literal is data[1]:
        CRef cr = i->cref;
        Clause& c = ca[cr];
        if(!c.isOneWatched()){
            printf("c wtf? size=%d lbd=%d oneWatched=%d received=%d\n", c.size(), c.lbd(), c.isOneWatched(), c.isReceived());
        }
        assert(c.isOneWatched());
        Lit false_lit = ~p;
        assert(c[0] == false_lit); // this is unary watch... No other choice if "propagated"
        //if (c[0] == false_lit)
        //c[0] = c[1], c[1] = false_lit;
        //assert(c[1] == false_lit);
        i++;
        Watcher w = Watcher(cr, c[0]);
        for (int k = 1; k < c.size(); k++) {
            if (value(c[k]) != l_False) {
                c[0] = c[k];
                c[k] = false_lit;
                unaryWatches[~c[0]].push(w);
                goto NextClauseUnary;
            }
        }

        // Did not find watch -- clause is empty under assignment:
        *j++ = w;

        confl = cr;
        qhead = trail.size();
        // Copy the remaining watches:
        while (i < end)
            *j++ = *i++;

        // We can add it now to the set of clauses when backtracking
        //printf("*");
        if (true) { //promoteOneWatchedClause) {
            //nbPromoted++;
            // Let's find the two biggest decision levels in the clause s.t. it will correctly be propagated when we'll backtrack
            int maxlevel = -1;
            int index = -1;
            for (int k = 1; k < c.size(); k++) {
                assert(value(c[k]) == l_False);
                assert(level(var(c[k])) <= level(var(c[0])));
                if (level(var(c[k])) > maxlevel) {
                    index = k;
                    maxlevel = level(var(c[k]));
                }
            }
            detachClausePurgatory(cr, true);
            assert(index != -1);
            Lit tmp = c[1];
            c[1] = c[index], c[index] = tmp;
            attachClause(cr);
            ca[cr].setOneWatched(false);
        }
NextClauseUnary:
        ;
    }
    ws.shrink(i - j);

    return confl;
}

/*_________________________________________________________________________________________________
         * |
         * |  reduceDB : ()  ->  [void]
         * |
         * |  Description:
         * |    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
         * |    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
         * |________________________________________________________________________________________________@*/
struct reduceDB_lt {
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {

        // Main criteria... Like in MiniSat we keep all binary clauses
        if(ca[x].size()> 2 && ca[y].size()==2) return 1;

        if(ca[y].size()>2 && ca[x].size()==2) return 0;
        if(ca[x].size()==2 && ca[y].size()==2) return 0;

        // Second one  based on literal block distance
        if(ca[x].lbd()> ca[y].lbd()) return 1;
        if(ca[x].lbd()< ca[y].lbd()) return 0;


        // Finally we can use old activity or size, we choose the last one
        return ca[x].activity() < ca[y].activity();
        //return x->size() < y->size();

        //return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); }
    }
};
int getMedian(std::vector<int> & tmp)
{
    if(tmp.size() <= 0)
        return 0;
    std::sort(tmp.begin(), tmp.end());
    return tmp[tmp.size()/2];
}

void Solver::analyzePermanent(){
    std::map<int, long> countByLBD, countBySize;
    std::map<int, long> agesByLBD, agesBySize, unusedByLBD, unusedBySize;

    for(int i = 0 ; i < permanentlyKeptLearntClauses.size();i++){
        Clause & c = ca[permanentlyKeptLearntClauses[i]];
        countByLBD[c.lbd()]++;
        countBySize[c.size()]++;
        agesByLBD[c.lbd()]      += conflicts - c.getLastTouched();
        agesBySize[c.size()]    += conflicts - c.getLastTouched();
        if(!c.wasUsed()){
            unusedByLBD[c.lbd()]++;
            unusedBySize[c.size()]++;
        }
    }
    printf("c stats by LBD: \n");
    for(std::map<int, long>::iterator it = countByLBD.begin() ; it != countByLBD.end();it++){
        long num = it->second;
        printf("c LBD %d: num %ld unused %ld average age %ld \n", it->first, it->second, unusedByLBD[it->first], agesByLBD[it->first] / num);
    }
    printf("c stats by size: \n");
    for(std::map<int, long>::iterator it = countBySize.begin() ; it != countBySize.end();it++){
        int num = it->second;
        printf("c size %d: num %ld unused %ld average age %ld \n", it->first, it->second, unusedBySize[it->first], agesBySize[it->first] / num);
    }
}
void Solver::reduceDB()
{

    int     i, j;
    nbReduceDB++;
    double t = MPI_Wtime();
    if(use_chanseok_style){
        // Okay, consider the following arrays:
        // - received.
        // - permanentlyKept;
        // - mediumLBD
        // - activity

        // Parameters:
        //     LBD core <- clauses with lbd of at most this value will be kept permanently
        //     usage_1  <- clauses which are either learnt locally, or received and have been used, will be kept for this many conflicts
        //     useage_2 <- received clauses will be kept until this number of conflicts
        //    Remove half of activity-based learnt clauses with lower activity, unless their LBD has dropped to some threshold


        int totalDeleted = 0;
        int promoted = 0;
        for(i=j=0 ; i < mediumLBDClauses.size();i++){
            Clause & c = ca[mediumLBDClauses[i]];
            if(c.lbd() <= opt_threshold_permanent){
                promoted++;
                permanentlyKeptLearntClauses.push(mediumLBDClauses[i]);
            }
            else if(!c.canBeDel() ||  locked(c) ||  c.getLastTouched() + opt_protect_learnts > conflicts)
                mediumLBDClauses[j++] = mediumLBDClauses[i];
            else{
                removeClause(mediumLBDClauses[i]);
            }
        }
        totalDeleted += i-j;
        mediumLBDClauses.shrink(i-j);


        for(i=j=0 ; i < receivedClauses.size();i++){
            Clause & c = ca[receivedClauses[i]];
            if(c.lbd() <= opt_threshold_permanent && !c.isOneWatched()){
                promoted++;
                permanentlyKeptLearntClauses.push(receivedClauses[i]);
                if(c.isOneWatched()){
                    printf("c promoting one-watched clause to permanent storage! \n");
                }
            }
            else if(!c.canBeDel() || locked(c) || c.getLastTouched() + opt_protect_receiveds > conflicts)
                receivedClauses[j++] = receivedClauses[i];
            else
                removeClause(receivedClauses[i]);
        }
        receivedClauses.shrink(i-j);
        totalDeleted += i-j;

        int permActzero = 0;
        double averageAge = 0;
        std::vector<int> ages;
        for(int i = 0 ; i < permanentlyKeptLearntClauses.size();i++){
            Clause & c = ca[permanentlyKeptLearntClauses[i]];
            if(c.activity() <= 0)
                permActzero++;
            if(c.getLastTouched() > conflicts)
                fprintf(stderr, "last touched is %d, but conflicts %llu clause is received: %d! \n", c.getLastTouched(), conflicts, c.isReceived());
            assert(conflicts >= c.getLastTouched());
            assert(c.getLastTouched() >= 0);
            averageAge += (double)(conflicts - c.getLastTouched())/permanentlyKeptLearntClauses.size();
            ages.push_back(conflicts - c.getLastTouched());
        }
        int median = getMedian(ages);
        if(procId == 0 && (threadId == 0 || (opt_subSimpCheck && threadId <= 1))){
            int cols = 0;
            if(opt_hashTest)
                cols = checkPermanentsWithHashes(26843543);
            if(cols > 1000){
                printf("c had many collisions, re-checking with larger number: \n");
                checkPermanentsWithHashes(268435459);
            }

            printf("c process %d, thread %d: have %d permanent, %d local, %d received clauses, %d activity based. Deleted %d clauses, conflicts: %llu actZero: %d average age %lf median %d time was %lf collisions %d\n", procId, threadId, permanentlyKeptLearntClauses.size(), mediumLBDClauses.size(), receivedClauses.size(), activityWatchedClauses.size(), totalDeleted-promoted, conflicts, permActzero, averageAge, median, MPI_Wtime()-t, cols);

            //analyzePermanent();
        }
    }
    else{
        sort(learnts, reduceDB_lt(ca));

        // We have a lot of "good" clauses, it is difficult to compare them. Keep more !
        if(ca[learnts[learnts.size() / RATIOREMOVECLAUSES]].lbd()<=3) nbclausesbeforereduce +=specialIncReduceDB;
        // Useless :-)
        if(ca[learnts.last()].lbd()<=5)  nbclausesbeforereduce +=specialIncReduceDB;


        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // Keep clauses which seem to be usefull (their lbd was reduce during this sequence)

        int limit = learnts.size() / 2;
        for (i = j = 0; i < learnts.size(); i++){
            Clause& c = ca[learnts[i]];
            if (c.lbd()>2 && c.size() > 2 && c.canBeDel() &&  !locked(c) && (i < limit)) {
                removeClause(learnts[i]);
                nbRemovedClauses++;
            }
            else {
                if(!c.canBeDel()) limit++; //we keep c, so we can delete an other clause
                c.setCanBeDel(true);       // At the next step, c can be delete
                learnts[j++] = learnts[i];
            }
        }
        //   printf("c have %d stuck local, and %d stuck global clauses! \n", stuck_local, stuck_recv);
        learnts.shrink(i - j);
        int oneWatched = 0;
        int promoted = 0;
        int promotedLBD = 0;
        int promotedSize = 0;
        int allLBD = 0;
        int allSize = 0;
        int actGTzero = 0;
        int promSize2 = 0;
        int nbDeleted = 0;
        for( i = j = 0 ; i < receivedClauses.size();i++){
            Clause & c = ca[receivedClauses[i]];
            if(c.lbd() <= 2){
                // Okay, copy it to the normal clauses!
                if(c.size() <= 2)
                    promSize2++;
                learnts.push(receivedClauses[i]);
                promoted++;
                promotedLBD += c.lbd();
                promotedSize += c.size();
            }
            else{
                int age = conflicts - c.getLastTouched();
                if(!locked(c) && age > opt_protect_receiveds && c.activity() <= 0){
                    // Okay, delete it
                    if(c.getOrigin() != threadId){
                        //coop->clauseDeleted(threadId, c.getOrigin(), c.getIndex());
                        nbDeleted++;
                    }
                    removeClause(receivedClauses[i]);
                }
                else{
                    receivedClauses[j++] = receivedClauses[i];
                }
            }


            if(c.activity() > 0)
                actGTzero++;
            allSize += c.size();
            allLBD += c.lbd();
            if(!c.isOneWatched()){
                //           promoted++;

            }
            else
                oneWatched++;
        }
        //   printf("c deleted %d of %d received clauses\n", i-j, i);
        receivedClauses.shrink(i-j);
        //   if(promoted > 0)
        if(verbosity >= 2)
            printf("c have %d received clauses, %d promoted, %d act>0,  avg LBD %lf, avg size %lf (all %lf, %lf), deleted %d\n", receivedClauses.size(), promoted, actGTzero,  (double)promotedLBD/promoted, (double)promotedSize/promoted, (double) allLBD/receivedClauses.size(), (double) allSize/receivedClauses.size(), nbDeleted);
    }
    //    else
    //     printf("c have %d received clauses...\n", receivedClauses.size());
    checkGarbage();
    //   if(threadId == 0){
    //       printf("c thread 0 imported %d binaries, out of which %d were redundant! \n", nbBinariesImported, nbRedundantBinaries);
    //   }
}

struct reduceDB_lt_Act {
    ClauseAllocator& ca;
    reduceDB_lt_Act(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) {

        return ca[x].activity() < ca[y].activity();
    }
};

void Solver::reduceActivityBasedClauses(){
    sort(learnts, reduceDB_lt_Act(ca));
    double t = MPI_Wtime();
    int i, j;
    int limit = activityWatchedClauses.size()/2;
    for(i = j = 0 ; i < activityWatchedClauses.size();i++){
        Clause & c = ca[activityWatchedClauses[i]];
        if(c.lbd() <= opt_threshold_mediumLBD)
            mediumLBDClauses.push(activityWatchedClauses[i]);
        else if (i < limit && !locked(c) && c.canBeDel())
            removeClause(activityWatchedClauses[i]);
        else{
            c.setCanBeDel(true);
            activityWatchedClauses[j++] = activityWatchedClauses[i];
        }
    }
    activityWatchedClauses.shrink(i-j);
    checkGarbage();
    if(procId == 0 && threadId == 0 && verbosity > 1)
        printf("c checked activity watched clauses, shrinked from %d to %d time was %lf \n", i, j, MPI_Wtime()-t);
}
void Solver::removeSatisfied(vec<CRef>& cs)
{

    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];


        if (satisfied(c))
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
         * |
         * |  simplify : [void]  ->  [bool]
         * |
         * |  Description:
         * |    Simplify the clause database according to the current top-level assigment. Currently, the only
         * |    thing done here is the removal of satisfied clauses, but more things can be put here.
         * |________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;
    //     printf("c in simplify now. threadId=%d, simpDB_assigns=%d, nAssigns=%d, simpDB_props=%d\n", threadId, nAssigns(), simpDB_assigns, simpDB_props);

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    removeSatisfied(receivedClauses);
    removeSatisfied(permanentlyKeptLearntClauses);
    removeSatisfied(mediumLBDClauses);
    removeSatisfied(activityWatchedClauses);

    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
         * |
         * |  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
         * |
         * |  Description:
         * |    Search for a model the specified number of conflicts.
         * |    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
         * |
         * |  Output:
         * |    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
         * |    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
         * |    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
         * |________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause,selectors;
    unsigned int nblevels,szWoutSelectors;
    bool blocked=false;
    starts++;
    int conflsWithoutImport = 0;
    int conflsNextExport = 100;
    int threshold_next_import = trail.size();
    for (;;){
        /*if(conflictC % 10 == 0){
            int m, s;
            coop->getNumStoredClauses(threadId , m, s);
            if(m > 1000 || s > 10000){
                printf("c have %d clauses pending (max: %d)\n", s, m);
            }
        }*/
        // Check:
        if(decisionLevel() == 0){
            int tsBefore = trail.size();
            propagateExtraUnits();
            extraUnits.clear();
            if(verbosity > 1 &&  trail.size() > tsBefore){
                printf("c solver %d imported %d unit clauses! \n", threadId, (trail.size()-tsBefore));
            }
        }
        CRef confl = propagate();
        if (confl != CRef_Undef){
            // CONFLICT

            conflicts++; conflictC++;conflictsRestarts++;
            // if(numProcesses > 1 &&  threadId == 0 &&  conflicts % 10 == 0){
            //   mpi_communication();
            // }
            if(useVSIDS && conflicts%5000==0 && var_decay<0.95)
                var_decay += 0.01;
            else if(!useVSIDS && step_size > min_step_size)
                step_size -= step_size_dec;

            if (verbosity >= 1 && conflicts%verbEveryConflicts==0 && threadId == 0){
                assert(starts > 0);

                printf("c | %8d %8d %7d  %5d | %7d %8d %8d | %5d %8d   %6d %8d | %6.3f %% |\n",
                       threadId,
                       (int)starts,(int)nbstopsrestarts, (int)(conflicts/starts),
                       (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals,
                       (int)nbReduceDB, nLearnts(), (int)nbDL2,(int)nbRemovedClauses, progressEstimate()*100);
            }
            if (decisionLevel() == 0) {
                //       printf("c thread %d writing answer FALSE\n", threadId);
                coop->answers[threadId] = l_False;
                return l_False;

            }

            trailQueue.push(trail.size());
            // BLOCK RESTART (CP 2012 paper)
            if( conflictsRestarts>LOWER_BOUND_FOR_BLOCKING_RESTART && lbdQueue.isvalid()  && trail.size()>R*trailQueue.getavg()) {
                lbdQueue.fastclear();
                nbstopsrestarts++;
                if(!blocked) {lastblockatrestart=starts;nbstopsrestartssame++;blocked=true;}
            }

            learnt_clause.clear();
            selectors.clear();
            analyze(confl, learnt_clause, selectors,backtrack_level,nblevels,szWoutSelectors);

            lbdQueue.push(nblevels);
            sumLBD += nblevels;


            cancelUntil(backtrack_level);

            if (certifiedUNSAT) {
                for (int i = 0; i < learnt_clause.size(); i++)
                    fprintf(certifiedOutput, "%i " , (var(learnt_clause[i]) + 1) *
                            (-2 * sign(learnt_clause[i]) + 1) );
                fprintf(certifiedOutput, "0\n");
            }
            if(coop->exportPolicy == EXPORT_VIVIFY_BEFORE && learnt_clause.size() > 2){
                // TODO: Only do this one some threads???
                if(nblevels <= coop->hard_limit_lbd && learnt_clause.size() <= coop->hard_limit_size){
                    std::vector<int> clause2Check;
                    for(int i = learnt_clause.size()-1 ; i >= 0;i--)
                        clause2Check.push_back(toInt(learnt_clause[i]));
                    clauseVivificationBuffer.push_back(std::make_pair(conflicts , clause2Check));
                }
            }
            else{
                exportClause(coop, learnt_clause, nblevels);
            }
            //         if(threadId == 0 && learnt_clause.size() == 2)
            //             addBinary2BIG(learnt_clause[0], learnt_clause[1]);
            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);nbUn++;
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                ca[cr].setLBD(nblevels);
                ca[cr].setSizeWithoutSelectors(szWoutSelectors);
                if(nblevels<=2) nbDL2++; // stats
                if(ca[cr].size()==2) nbBin++; // stats
                assert(ca[cr].getLastTouched() == 0);

                ca[cr].setLastTouched(conflicts);
                if(!use_chanseok_style)
                    learnts.push(cr);
                else {
                    if(nblevels <= opt_threshold_permanent)
                        permanentlyKeptLearntClauses.push(cr);
                    else if(nblevels <= opt_threshold_mediumLBD)
                        mediumLBDClauses.push(cr);
                    else
                        activityWatchedClauses.push(cr);
                }
                attachClause(cr);

                claBumpActivity(ca[cr]);
                uncheckedEnqueue(learnt_clause[0], cr);
            }
            varDecayActivity();
            claDecayActivity();
            lbool answer = l_Undef;
            if(conflsWithoutImport > 5 && coop->oneWatchedImport){
                answer = importClauses(coop);
                conflsWithoutImport = 0;
            }
            else if(opt_clauseImportBetweenRestarts){
                if(opt_lowLLevelClauseImport){
                    if(decisionLevel() <= 1 ||  trail.size() < threshold_next_import){
                        int dlBeforeImport = decisionLevel();
                        answer = importClauses(coop);
                        if(decisionLevel() < dlBeforeImport && verbosity > 1)
                            printf("c imported some clauses after %d conflicts without check, DL %d -> %d\n", conflsWithoutImport, dlBeforeImport, decisionLevel());
                        threshold_next_import = decisionLevel()==0?trail.size() : trail_lim[0];
                        conflsWithoutImport=0;
                    }
                    else{
                        threshold_next_import += 1 + trailQueue.getavg()>>7;
                        conflsWithoutImport++;
                    }
                }
                else{
                    answer = importClauses(coop);
                    //                 printf("c imported some clauses after %d conflicts without check, DL %d -> %d\n", conflsWithoutImport, dlBeforeImport, decisionLevel());
                }
            }
            if(answer != l_Undef){
                return answer;
            }

        }else{
            int budget = 1000 * 1000;//assumptions.size() < 4 ? 1000 : assumptions.size() < 7 ? 10 * 1000 : 1000*1000;
            if(runningCnC &&
                    (conflicts > conflictsLastCubeStarted + budget
                     || (coop->stealRequestPending[threadId] && conflicts > conflictsLastCubeStarted + 1000))){

                if(decisionLevel() > assumptions.size()){
                    if(coop->stealRequestPending[threadId]){
                        printf("c steal request pending, thread %d process %d conflicts %llu conflictsLastCubeStarted %d\n", threadId, procId, conflicts, conflictsLastCubeStarted);
                    }
                    coop->stealRequestPending[threadId] = false;

                    if(createNewJobs(true) == false){
                        cancelUntil(0);
                        return l_Undef;
                    }
                    else{
                        conflictsLastCubeStarted = conflicts;
                    }
                }
                else{
                    bool debug = true;
                    if(debug){
                        printf("c cannot create new job as DL is too small! \n");
                    }
                }
            }
            // Our dynamic restart, see the SAT09 competition compagnion paper
            if (asynch_interrupt ||
                    (nof_conflicts <= 0 &&  lbdQueue.isvalid() && ((lbdQueue.getavg()*K) > (sumLBD / conflictsRestarts)))) {
                lbdQueue.fastclear();
                progress_estimate = progressEstimate();
                int bt = 0;
                if(incremental) { // DO NOT BACKTRACK UNTIL 0.. USELESS
                    bt = (decisionLevel()<assumptions.size()) ? decisionLevel() : assumptions.size();
                }
                cancelUntil(bt);
                return l_Undef; }
            else if(nof_conflicts > 0 && conflictC > nof_conflicts){
                cancelUntil(0);
                return l_Undef;
            }


            if(decisionLevel() == 0){
                lbool answer = importClauses(coop);
                conflsWithoutImport=0;
                if(answer != l_Undef)
                    return answer;
                if(extraUnits.size() > 0){
                    if(verbosity > 1)
                        printf("c have %d units on the queue now, continueing! \n", extraUnits.size());
                    continue;
                }
                if(answer == l_Undef && clauseVivificationBuffer.size() > 0 && conflictC > conflsNextExport ){
                    conflsNextExport = conflictC + 100;
                    //int nbBefore = clauseVivificationBuffer.size();
                    answer = vivifyAndExportClauses();
                    //printf("c have long restart interval (%d), exported %d clauses from vivification buffer\n", conflictC, nbBefore - clauseVivificationBuffer.size());
                    if(answer != l_Undef){
                        coop->answers[threadId] = l_False;
                        return answer;
                    }
                }
            }
            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify()) {
                return l_False;
            }

            // Do clause DB reductions in a regular interval!
            if(use_chanseok_style){
                if(activityWatchedClauses.size() > maxActivitySize){
                    reduceActivityBasedClauses();
                }
                if(conflicts > conflicts_next_reduce){
                    reduceDB();
                    conflicts_next_reduce += conflicts_reduce_interval;
                }
            }
            else{
                if(conflicts>=curRestart* nbclausesbeforereduce)
                {
                    if(learnts.size() > 0){
                        //             assert(learnts.size()>0);
                        curRestart = (conflicts/ nbclausesbeforereduce)+1;
                        reduceDB();
                        nbclausesbeforereduce += incReduceDB;
                    }
                }
            }


            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    bool exportFinals = true;
                    if(exportFinals){
                        exportClause(coop, conflict, 0);
                    }
                    printf("c cube length %d conflict.size()=%d\n", assumptions.size(), conflict.size());
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;

                next = pickBranchLit();

                if (next == lit_Undef){
                    printf("c last restart ## conflicts  :  %d %d \n",conflictC,decisionLevel());
                    printf("c thread %d found answer TRUE , nVars()=%d, trail.size()=%d\n", threadId,  nVars(), trail.size());
                    // Model found:
                    bool debug = true;
                    if(debug){
                        for(int i = 0 ; i < clauses.size();i++){
                            if(!satisfied(ca[clauses[i]])){
                                printf("c model is not valid, this clause is not satisfied! \n");
                            }
                        }
                    }
                    coop->answers[threadId] = l_True;
                    return l_True;
                }
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

void Solver::printIncrementalStats() {

    printf("c---------- Glucose Stats -------------------------\n");
    printf("c restarts              : %jd\n", starts);
    printf("c nb ReduceDB           : %jd\n", nbReduceDB);
    printf("c nb removed Clauses    : %jd\n",nbRemovedClauses);
    printf("c nb learnts DL2        : %jd\n", nbDL2);
    printf("c nb learnts size 2     : %jd\n", nbBin);
    printf("c nb learnts size 1     : %jd\n", nbUn);

    printf("c conflicts             : %jd \n",conflicts);
    printf("c decisions             : %jd\n",decisions);
    printf("c propagations          : %jd\n",propagations);

    printf("c SAT Calls             : %d in %g seconds\n",nbSatCalls,totalTime4Sat);
    printf("c UNSAT Calls           : %d in %g seconds\n",nbUnsatCalls,totalTime4Unsat);
    printf("c--------------------------------------------------\n");


}

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

void Solver::createBIG(){
    if(!USE_BIG_STUFF)
        return;
    double tStart = MPI_Wtime();
    if(big_edges.size() == 0){
        big_edges.insert(big_edges.end(), 2*nVars(), std::set<int>());
    }
    for(int i = 0 ; i < clauses.size();i++){
        Clause & c = ca[clauses[i]];
        if(c.size() <= 2){
            Lit l1 = c[0];
            Lit l2 = c[1];
            if(value(l1) == l_Undef && value(l2) == l_Undef){
                addBinary2BIG(l1, l2);
            }
        }
    }
    printf("c created BIG, time was %lf\n", MPI_Wtime()-tStart);
}

void Solver::addBinary2BIG(Lit l1, Lit l2){
    if(!USE_BIG_STUFF)
        return;
    if(toInt(l1) < toInt(l2))
        knownBinaries.insert(std::make_pair(toInt(l1), toInt(l2)));
    else
        knownBinaries.insert(std::make_pair(toInt(l2), toInt(l1)));
    big_edges[toInt(~l1)].insert(toInt(l2));
    big_edges[toInt(~l2)].insert(toInt(l1));
}
bool Solver::redundantBinary(Lit l1, Lit l2){
    if(!USE_BIG_STUFF)
        return false;
    // Check if there is a path from (not l1) to l2. In that case, the binary is redundant!
    int index = 0;
    std::vector<int> q;
    MYFLAG++;
    int iters = 0;
    q.push_back(toInt(~l1));
    permDiff[toInt(~l1)] = MYFLAG;
    while(index < q.size()){
        if(iters > 1000){
            printf("c wtf had a huge amount of iterations (%d), queue size is %lu, quitting here! \n", iters, q.size());
            return false;
        }
        int next = q[index++];
        if(next == toInt(l2))
            return true;
        for(std::set<int>::iterator it = big_edges[next].begin() ; it != big_edges[next].end();it++){
            if(permDiff[*it] != MYFLAG){
                permDiff[*it] = MYFLAG;
                q.push_back(*it);
            }
        }
    }

    return false;
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{

    if(incremental && certifiedUNSAT) {
        printf("Can not use incremental and certified unsat in the same time\n");
        exit(-1);
    }
    model.clear();
    conflict.clear();
    remove_satisfied = true;
    if (!ok) return l_False;
    double curTime = cpuTime();

    nbClausesExported = 0;
    nbClausesLifted = 0;
    // Update the size of the trail - this will be the same for all solvers at this point!
    tailUnitLit = trail.size();
    //     printf("c thread %d starting with trail size %d and %d clauses\n", threadId, tailUnitLit, clauses.size());
    if(threadId == 0){
        //         createBIG();
        //         nbBinariesImported=0;
        //         nbRedundantBinaries=0;
    }
    solves++;

    int globalId = coop->getThreadIndex(procId, threadId);
    fl_check_iterations = 0;

    int restartMode = globalId %3 == 0 ? RESTART_INNER_OUTER :
                                         globalId %3 == 1 ? RESTART_LUBY : RESTART_GLUCOSE_DEFAULT;
    if(!opt_restartPortfolio)
        restartMode = RESTART_GLUCOSE_DEFAULT;
    int inner = 100,  outer = 100;

    if(opt_restartPortfolio){
        /* Diversify portfolio.
                 *  - DO NOT use LRB with glucose's restart heuristic!
                 *  - Half of the solvers use chanseOk config, others glucose default
                 *  -
                */
        int tmp = threadId;
        use_chanseok_style = tmp & 1;
        tmp >>= 1;
        switch(tmp & 0x3){
        case 0:
            // Default, do nothing
            restartMode = RESTART_GLUCOSE_DEFAULT;
            break;
        case 1:
            restartMode = RESTART_LUBY;
            break;
        case 2:
            restartMode = RESTART_LUBY;
            useVSIDS = false;
            break;
        case 3:
            restartMode = RESTART_INNER_OUTER;
            useVSIDS = false;
            break;
        }
        if(procId == 0 && verbosity > 1){
            printf("c thread %d clause DB %d restart %d vsids %d\n", threadId, use_chanseok_style, restartMode, useVSIDS);
        }
    }

    lbool   status        = l_Undef;
    if(!incremental && verbosity>=1 && threadId == 0 && procId == 0) {
        printf("c ========================================[ MAGIC CONSTANTS ]==============================================\n");
        printf("c | Constants are supposed to work well together :-)                                                      |\n");
        printf("c | however, if you find better choices, please let us known...                                           |\n");
        printf("c |-------------------------------------------------------------------------------------------------------|\n");
        printf("c |                                |                                |                                     |\n");
        printf("c | - Restarts:                    | - Reduce Clause DB:            | - Minimize Asserting:               |\n");
        printf("c |   * LBD Queue    : %6d      |   * First     : %6d         |    * size < %3d                     |\n",lbdQueue.maxSize(),nbclausesbeforereduce,lbSizeMinimizingClause);
        printf("c |   * Trail  Queue : %6d      |   * Inc       : %6d         |    * lbd  < %3d                     |\n",trailQueue.maxSize(),incReduceDB,lbLBDMinimizingClause);
        printf("c |   * K            : %6.2f      |   * Special   : %6d         |                                     |\n",K,specialIncReduceDB);
        printf("c |   * R            : %6.2f      |   * Protected :  (lbd)< %2d     |                                     |\n",R,lbLBDFrozenClause);
        printf("c |                                |                                |                                     |\n");
        printf("c ==================================[ Search Statistics (every %6d conflicts) ]=========================\n",verbEveryConflicts);
        printf("c |                                                                                                       |\n");

        printf("c |          RESTARTS           |          ORIGINAL         |              LEARNT              | Progress |\n");
        printf("c |  tId  NB   Blocked  Avg Cfc |    Vars  Clauses Literals |   Red   Learnts    LBD2  Removed |          |\n");
        printf("c =========================================================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    int conflsNextSubsCheck = 10000;
    int increase = 10000;
    int nbCheckCalls = 0;
    while (status == l_Undef){
        int limit = 0;
        if(restartMode == RESTART_LUBY){
            limit = luby(2, curr_restarts)*100;
            //printf("c luby: %d\n", limit);
        }
        else if(restartMode == RESTART_INNER_OUTER){
            if(inner > outer){
                inner = 100; outer*=1.1;
            }
            else
                inner*=1.1;
            limit = inner;
        }
        checkCnCState();
        int nbConflsBefore = conflicts;
        status = search(limit); // the parameter is useless in glucose, kept to allow modifications

        if(status == l_Undef && opt_PromoteOneWatched){
            promoteOneWatched();
        }
        if(status == l_False && runningCnC){
            notifyFailedCubes();    // Tell comm-thread about this progress:
            assumptions.clear();
            runningCnC = false;
            if(conflict.size() > 0)     // If this conflict is not independent of assumptions, continue search:
                status = l_Undef;
        }

        if (!withinBudget()) break;
        curr_restarts++;
        if(status == l_Undef && clauseVivificationBuffer.size() > 0){
            status = vivifyAndExportClauses();
            if(status == l_False){
                coop->answers[threadId]=l_False;
            }
        }
        if(opt_subSimpCheck && procId == 0 && threadId == 0 && status == l_Undef && use_chanseok_style && permanentlyKeptLearntClauses.size() > 1000 && conflicts > conflsNextSubsCheck){
            printf("c now calling subsimp. was scheduled for %d conflicts %d conflicts in last search %d\n", conflsNextSubsCheck, conflicts, conflicts - nbConflsBefore);
            conflsNextSubsCheck += increase;
            increase += 1000;
            nbCheckCalls++;
            bool fullCheck = opt_FullubSimpCheck ||  (nbCheckCalls % 10 == 0);
            SimpSolver * ss = dynamic_cast<SimpSolver*> (this);
            if(ss){
                bool retSubs = ss->checkPermanentForSubsumption(fullCheck);
                if(!retSubs){
                    printf("c backward subsumption check on permanent clauses return false! \n");
                }
            }
            else
                printf("c could not cast! \n");
        }
        /*else if(opt_hashTest && conflicts > conflsNextSubsCheck && status == l_Undef && procId == 0 && threadId == 0){
            conflsNextSubsCheck += increase;
            increase += 1000;
            checkPermanentsWithHashes(26843543);
        }*/
//        if(status == l_Undef){
//            if(fl_check_iterations < 3){
//                int tsBefore = trail.size();
//                printf("c starting FL stuff! \n");
//                lbool tmp = fl_check_parallel(globalId, numSolver,  nextIndex, 2000);
//                printf("c process %d thread %d fl_check done trailSize %d -> %d nextIndex = %d \n", procId, threadId, tsBefore, trail.size(), nextIndex);
//                if(tmp == l_False){
//                    printf("c found UNSAT during FL check! \n");
//                    status = l_False;
//                }
//                if(fl_check_iterations >= 3){
//                    printf("c done with FL check! \n");
//                }
//            }
//        }
    }
    if(verbosity > 1)
        printf("c thread %d writing answer (%d lifted, %d exported, %llu conflitcs )\n", threadId, nbClausesLifted, nbClausesExported, conflicts);
    //printf("c buffer sizes are %d %d %d\n", coop->clausesSent.size(), coop->clausesLifted.size(), coop->conflicts.size());
    coop->clausesSent[threadId] = nbClausesExported;
    coop->clausesLifted[threadId] = nbClausesLifted;
    coop->conflicts[threadId] = conflicts;
    if(verbosity >= 2)
        printf("c solver thread %d found solution! \n", threadId);
    if (!incremental && verbosity >= 2)
        printf("c =========================================================================================================\n");


    if (certifiedUNSAT){ // Want certified output
        if (status == l_False)
            fprintf(certifiedOutput, "0\n");
        fclose(certifiedOutput);
    }

    if(threadId == 0 && status != l_Undef &&  coop->globalResult == l_Undef && numProcesses > 1){
        coop->globalResult = status;
    }
    if(verbosity > 1)
        printf("c trhread %d status %c coop->answers[threadId]=%c\n", threadId, status == l_True ? '1' : (status == l_False ? '0' : '?'), coop->answers[threadId] == l_True ? '1' : (coop->answers[threadId] == l_False ? '0' : '?'));
    if (status == l_True && coop->answers[threadId] == l_True){
        // Extend & copy model:
        printf("c thread %d growing model to %d\n", threadId, nVars());
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
        storeModel();

    }else if (status == l_False && conflict.size() == 0)
        ok = false;



    cancelUntil(0);

    double finalTime = cpuTime();
    if(status==l_True) {
        nbSatCalls++;
        totalTime4Sat +=(finalTime-curTime);
    }
    if(status==l_False) {
        nbUnsatCalls++;
        totalTime4Unsat +=(finalTime-curTime);
    }
#ifdef GLOBAL_DEBUG
    printf("c process %d, thread %d terminating with status %c\n", procId, threadId, ((status == l_True ? '1' : (status == l_False ? '0' : '?'))));
#endif

    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
//
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;

    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    //printf("c reloc called! \n");
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    watchesBin.cleanAll();
    unaryWatches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
            vec<Watcher>& ws2 = watchesBin[p];
            for (int j = 0; j < ws2.size(); j++)
                ca.reloc(ws2[j].cref, to);
            vec<Watcher>&ws3 = unaryWatches[p];
            for(int j = 0 ; j < ws3.size();j++)
                ca.reloc(ws3[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }


    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);


    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);

    // All permanently kept:
    for(int i = 0 ; i < permanentlyKeptLearntClauses.size();i++)
        ca.reloc(permanentlyKeptLearntClauses[i], to);

    // All medium LBD
    for(int i = 0 ; i < mediumLBDClauses.size();i++)
        ca.reloc(mediumLBDClauses[i], to);

    // All activity based learnts:
    for(int i = 0 ; i < activityWatchedClauses.size();i++)
        ca.reloc(activityWatchedClauses[i], to);

    // All received:
    for(int i = 0 ; i < receivedClauses.size();i++)
        ca.reloc(receivedClauses[i], to);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted());

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n",
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}




/*
         * Return
         *  - l_True, if clause was shrinked
         *  - l_Undef, if nothing happend
         *  - l_False, if UNSAT has been detected
         * */

int Solver::vivifyAndExport(std::vector<int> & c){
    assert(0 == decisionLevel());
    bool DEBUG_CHECK_ENTAILED = true;

    for(int i = 0 ; i < c.size();i++){
        Lit p = toLit(c[i]);
        if(value(p) == l_True && level(var(p)) == 0)
            return SATISFIED;
    }
    vec<Lit> ps;
    int skipped = 0;
    for(int i = 0 ; i < c.size();i++){
        Lit p = toLit(c[i]);
        if(value(p) == l_Undef){
            // TODO: Branch & see what happened!
            ps.push(p);
            newDecisionLevel();
            uncheckedEnqueue(~p);
            CRef confl = propagate();
            if(confl != CRef_Undef){

                // TODO: CHECK: I can either return the conflict clause here, or backtrack. Then, this will propagate the opposite value of c[i], and I can run analyzeFinal... does this give a better result???
                vec<Lit> out_learnt;
                analyze_vivification(confl, out_learnt);

                if(out_learnt.size() == 1){
                    // Okay, found a unit clause. This will be exported anyways, don't do anything here unless UNSAT was found!
                    cancelUntil(0);
                    if(DEBUG_CHECK_ENTAILED)
                        assert(entailed(out_learnt));
                    uncheckedEnqueue(out_learnt[0]);
                    if(propagate() == CRef_Undef)
                        return CONFLICT;
                    else
                        return FORMULA_UNSAT;
                }
                else{
                    // Okay, export the resulting conflict clause, and backtrack
                    cancelUntil(0);
                    if(DEBUG_CHECK_ENTAILED)
                        assert(entailed(out_learnt));
                    exportClause(coop, out_learnt, 2);          // TODO: Can I just assume some LBD here? Which should I use?
                    return CONFLICT;
                }
            }
        }
        else if(value(p) == l_True){

            int tomin = i;
            for(int j = 0 ; j < c.size();j++){
                if(value(toLit(c[j])) == l_True && level(var(toLit(c[j]))) < level(var(toLit(c[tomin]))))
                    tomin = j;
            }
            /*if(tomin != i){
                printf("c changed index from %d to %d! (DL %d -> %d)\n", i, tomin, level(var(toLit(c[i]))), level(var(toLit(c[tomin]))));
            }*/
            assert(value(toLit(c[tomin])) == l_True);
            if(level(var(toLit(c[tomin]))) < decisionLevel()){
                cancelUntil(level(var(toLit(c[tomin]))));
            }
            ps.clear();
            assert(value(toLit(c[tomin])) == l_True);
            analyzeFinal(toLit(c[tomin]), ps);
            cancelUntil(0);
            if(DEBUG_CHECK_ENTAILED)
                assert(entailed(ps));
            exportClause(coop, ps, 2);
            cancelUntil(0);
            return ps.size() < c.size() ? SHRINKED : NO_REDUCE;
        }
        else
            skipped++;
    }
    // Okay, looks like I forgot about this clause!
    cancelUntil(0);
    //if(DEBUG_CHECK_ENTAILED)
    //    assert(entailed(ps));
    exportClause(coop, ps, 2);
    cancelUntil(0);
    return SHRINKED;
}

lbool Solver::vivifyAndExportClauses(){
    assert(0 == decisionLevel());
    int old_phase = phase_saving;
    int old_ccmin = ccmin_mode;
    double oldVarInc = var_inc;
    bool oldVSIDS = useVSIDS;
    useVSIDS = true;
    var_inc = 0;
    phase_saving = 0;
    std::vector<std::pair<int, std::vector<int> > > newBuffer;
    int delay_check = opt_delayBeforeCheck;
    int checked = 0;
    int reduced = 0;
    int numLiterals = 0;
    long propsBefore = propagations;
    double t = MPI_Wtime();
    for(int i = 0 ; i < clauseVivificationBuffer.size();i++){

        std::pair<int, std::vector<int> > & p = clauseVivificationBuffer[i];
        if(conflicts >= p.first + delay_check){
            checked++;
            nbClausesExported ++;
            numLiterals += clauseVivificationBuffer[i].second.size();
            int succ = vivifyAndExport(clauseVivificationBuffer[i].second);
            if(succ == SHRINKED || succ == CONFLICT){
                nbClausesLifted++;
                reduced++;
            }
            if(FORMULA_UNSAT == succ)
                return l_False;
        }
        else
            newBuffer.push_back(p);
    }

    /* Restore old settings: */
    phase_saving = old_phase;
    ccmin_mode = old_ccmin;
    var_inc = oldVarInc;
    useVSIDS = oldVSIDS;
    assert(ccmin_mode == opt_ccmin_mode);

    long propsUsed = propagations - propsBefore;

    clauseVivificationBuffer.clear();
    clauseVivificationBuffer.insert(clauseVivificationBuffer.end(), newBuffer.begin(), newBuffer.end());
    double avgSize = checked > 0 ? ((double) numLiterals)/checked : 0;
    //             printf("ran clause vivification, checked %d clauses and reduced %d\n", checked, reduced);
    if(verbosity >= 2)
        printf("c vivification took time %lf, checked %d clauses with average size %lf, had %ld propagations \n", MPI_Wtime()-t, reduced, avgSize, propsUsed);
    sumOfReductionTimes += MPI_Wtime()-t;
    assert(0 == decisionLevel());
    return l_Undef;
}


void Solver::checkCnCState(){
    bool debug = true;
    //             printf("c thread %d: checkCnCState! \n", threadId);
    if(runningCnC){
        // Check if a time-out occured. If so, store "newCube" to cooperation thread, and clear assumptions.
        if(newCube.size() > 0){
            pthread_mutex_lock(& coop->cube_lock);
            // TODO: Should I make this depend on some strategy?
            std::vector<int> v;
            for(int i = 0 ; i < newCube.size();i++)
                v.push_back(toInt(newCube[i]));
            coop->newCubesForMaster.push_back(v);
            coop->newFreeSlaves.push_back(coop->getThreadIndex(procId, threadId));
            pthread_mutex_unlock(& coop->cube_lock);
            if(debug){
                printf("c send cube of size %lu back to cooperation! \n", v.size());
            }
            assumptions.clear();
            newCube.clear();
            runningCnC=false;
        }
    }
    else if(!runningCnC){
        //               printf("c checking cubePending for threadId %d\n", threadId);
        assert(coop);
        assert(coop->cubePending);
        if(coop->cubePending[threadId]){
            printf("c thread %d received cube of size %lu\n", threadId, coop->newCubesForSlave[threadId].size());
            assert(0 == decisionLevel());
            pthread_mutex_lock(& coop->cube_lock);
            assert(assumptions.size() == 0);
            for(int i = 0 ; i < coop->newCubesForSlave[threadId].size() ; i++)
                assumptions.push(toLit(coop->newCubesForSlave[threadId][i]));
            if(debug)
                printf("c added cube of size %d\n", assumptions.size());
            coop->cubePending[threadId]=false;
            coop->newCubesForSlave[threadId].clear();
            pthread_mutex_unlock(& coop->cube_lock);
            runningCnC=true;
            conflictsLastCubeStarted = conflicts;
        }
    }
    //             printf("c checkCnCState done! \n");
}

void Solver::notifyFailedCubes(){
    // Tell the communication thread that this cube failed:
    
    bool debug = true;
    if(debug){
        printf("c notificationFailedCubes, DL=%d\n", decisionLevel());
        printf("c notify failed cubes! \n");
    }
    
    pthread_mutex_lock(& coop->cube_lock);
    coop->notificationFailedCubes.push_back(std::make_pair(threadId, (int) assumptions.size()));
    coop->newFreeSlaves.push_back(coop->getThreadIndex(procId, threadId));
    if(debug)
        printf("c notifying com-thread about failed cube of size %d\n", assumptions.size());
    pthread_mutex_unlock(& coop->cube_lock);
    cancelUntil(0);
    assumptions.clear();
    
}


void Solver::switchMode   (branchingHeuristic b){
    assert(0 == decisionLevel());
    if(useVSIDS && b==VSIDS)
        return;
    if(!useVSIDS && b==LRB)
        return;
    if(b == LRB){
        double maxPrio = activity[order_heap[0]];
        if(maxPrio > 0){
            for(int i = 0 ; i < nVars();i++){
                assert(activity[i] <= maxPrio);
                activity[i] /= maxPrio;
            }
        }
    }
    else{
        // Just keep LRB activities as initial values for VSIDS?
    }
}

bool Solver::createNewJobs(bool keepRunning){
    std::vector<int> newJob;
    for(int i = 0 ; i < assumptions.size();i++)
        newJob.push_back(toInt(assumptions[i]));
    pthread_mutex_lock(& coop->cube_lock);
    
    for(int i = 0 ; i < 3 && assumptions.size() < decisionLevel() ; i++){
        Lit nextLit = trail[trail_lim[assumptions.size()]];
        assert(reason(var(nextLit)) == CRef_Undef);
        assert(level(var(nextLit)) == assumptions.size()+1);
        std::vector<int> toShare(newJob.begin(), newJob.end());
        toShare.push_back(toInt(~nextLit));
        coop->newCubesForMaster.push_back(toShare);
        newJob.push_back(toInt(nextLit));
        assumptions.push(nextLit);
    }
    if(!keepRunning){
        coop->newFreeSlaves.push_back(coop->getThreadIndex(procId, threadId));
        coop->newCubesForMaster.push_back(newJob);
        assumptions.clear();
    }
    else{
        assert(assumptions.size() == newJob.size());
        for(int i = 0 ; i < assumptions.size();i++)
            assert(toInt(assumptions[i]) == newJob[i]);
    }
    pthread_mutex_unlock(& coop->cube_lock);
    return keepRunning;
}


lbool Solver::fl_check(Lit l){
    assert(0 == decisionLevel());
    if(fl_seen.size() == 0)
        fl_seen.resize(2*nVars(), false);
    if(value(l) != l_Undef)
        return l_Undef;
    newDecisionLevel();
    uncheckedEnqueue(l);
    CRef confl = propagate();
    if(confl != CRef_Undef){
        cancelUntil(0);
        assert(value(~l) == l_Undef);
        uncheckedEnqueue(~l);
        return propagate() == CRef_Undef ? l_True : l_False;

    }
    // Remember literals seen here
    for(int i = trail_lim[0] ; i < trail.size();i++)
        fl_seen[toInt(trail[i])]=true;
    cancelUntil(0);
    return l_Undef;
}

/*
 * Perform failed literal check on (some) literals --- the other solver threads will care for the others!
 * */

lbool Solver::fl_check_parallel(int globalThreadId, int numSolvers, int & nextIndex, int numChecks){
    lbool ret = l_Undef;
    int backup = phase_saving;
    // TODO: Also for LRB?
    double t = MPI_Wtime();
    for(int i = 0 ; i < numChecks ; i++){
        if(nextIndex >= nVars()){
            // Okay, I'm done with this iteration
            nextIndex = globalThreadId;
            fl_check_iterations++;
            return ret;
        }
        // TODO: Backtrack to some root of the BIG?
        if(decision[nextIndex]){
            Lit l = mkLit(nextIndex);
            // l = getRoot(l);
            lbool ret1 = fl_check(l);
            if(ret1 == l_False)
                return l_False;
            else if(ret1 == l_True)
                ret = l_True;
            ret1 = fl_check(~l);
            if(ret1 == l_False)
                return l_False;
            else if(ret1 == l_True)
                ret = l_True;
        }
        nextIndex += numSolvers;
    }
    phase_saving = backup;
    printf("c time for FL was %lf\n", MPI_Wtime() - t);
    return ret;
}

double Solver::estimateMemUsage(){
    double ret = 0.0;
    ret += ca.size()*ClauseAllocator::Unit_Size;
    ret += (clauses.size() * 8);        // Pointers to the clauses
    ret += (clauses.size() * 2 * 8);    // Watches and stuff
    ret += nVars() * 100;

    ret /= (1024.0 * 1024.0); // Make this MB
    return ret;
}

/*
 * Returns
 *      - l_Undef, if nothing has happened
 *      - l_True, if at least one clause was minimised
 *      - l_False, if it was found that the formula is unsatisfiable
 * */
lbool Solver::minimiseSomeRandomPermanents(int num2Reduce){
    lbool ret = l_Undef;
    if(permanentlyKeptLearntClauses.size() < 1000){
        return ret;
    }
    for(int i = 0 ; i < num2Reduce ; i++){
        int index = rand() % permanentlyKeptLearntClauses.size();
        Clause & c = ca[permanentlyKeptLearntClauses[index]];
    }

    return ret;
}

void Solver::promoteOneWatched(){
    int prom = 0;
    unaryWatches.cleanAll();
    for(int i = 0 ; i < receivedClauses.size();i++){
        CRef cr = receivedClauses[i];
        Clause & c = ca[cr];
        if(c.isOneWatched()){
            detachClausePurgatory(cr);
            attachClause(cr);
            ca[cr].setOneWatched(false);
            prom++;
        }
    }
    //printf("c promoted %d one-watched clauses! \n", prom);
    unaryWatches.cleanAll();
    bool debug = false;
    if(debug){
        for(int i = 0 ; i < 2*nVars();i++){
            vec<Watcher>& ws = unaryWatches[toLit(i)];
            for(int j = 0 ; j < ws.size();j++){
                CRef cr = ws[i].cref;
                if(ca[cr].isOneWatched() == false){
                    printf("c this is weird. Clause was just detached, but is still in watcher list! mark %d, recv %d, size %d\n", ca[cr].mark(), ca[cr].isOneWatched(), ca[cr].size());
                }
            }
        }
    }
}


size_t Solver::commutativeHashFunction(const Clause & c, int which, size_t numBits) {
        size_t res = 0;
        for (size_t j = 0; j < c.size(); j++) {
                int lit = toInt(c[j]);
                res ^= lit * primes[abs((which * lit) % NUM_PRIMES)];
        }
        return res % numBits;
}

int Solver::checkPermanentsWithHashes(size_t numBits){
    std::vector<bool> v1(numBits);
    std::vector<bool> v2(numBits);
    std::vector<bool> v3(numBits);
    std::vector<bool> v4(numBits);
    int collisions = 0;
    double tStart = MPI_Wtime();
    for(int i = 0 ; i < permanentlyKeptLearntClauses.size();i++){
        size_t h1 = commutativeHashFunction(ca[permanentlyKeptLearntClauses[i]], 1, numBits);
        size_t h2 = commutativeHashFunction(ca[permanentlyKeptLearntClauses[i]], 2, numBits);
        size_t h3 = commutativeHashFunction(ca[permanentlyKeptLearntClauses[i]], 3, numBits);
        size_t h4 = commutativeHashFunction(ca[permanentlyKeptLearntClauses[i]], 4, numBits);
        if(v1[h1] && v2[h2] && v3[h3] && v4[h4]){
            collisions++;
        }
        else{
            v1[h1]=true;
            v2[h2]=true;
            v3[h3]=true;
            v4[h4]=true;
        }
    }
    printf("c done with hash test. Used %d bits, time was %lf, collisions %d\n", numBits, MPI_Wtime()-tStart, collisions);
    return collisions;
}

/*
 * Return whether the clause "c" is entailed by this formula by checking that unit-propagation on its negation yields a conflict
 * */
bool Solver::entailed(vec<Lit> & c){
    assert(0 == decisionLevel());
    int tsBefore = trail.size();
    newDecisionLevel();
    for(int i = 0 ; i < c.size();i++){
        uncheckedEnqueue(~c[i]);
    }
    CRef confl = propagate();
    bool ret = confl != CRef_Undef;
    cancelUntil(0);
    assert(trail.size() == tsBefore);
    return ret;
}
