/*****************************************************************************************[Main.cc]
 Glucose -- Copyright (c) 2009, Gilles Audemard, Laurent Simon
                                CRIL - Univ. Artois, France
                                LRI  - Univ. Paris Sud, France

Glucose sources are based on MiniSat (see below MiniSat copyrights). Permissions and copyrights of
Glucose are exactly the same as Minisat on which it is based on. (see below).

---------------

Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>

#include <signal.h>
#include <zlib.h>
#include <sys/resource.h>
#include <mpi.h>

#include <pthread.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "core/Cooperation.h"
#include "simp/SimpSolver.h"

#include "../mtl/apple_barrier.h"

#include <iostream>
#include <vector>

using namespace Glucose;

//=================================================================================================


void printStats(Solver& solver)
{
    double cpu_time = cpuTime();
    double mem_used = 0;//memUsedPeak();
    printf("c restarts              : %"PRIu64" (%"PRIu64" conflicts in avg)\n", solver.starts,(solver.starts>0 ?solver.conflicts/solver.starts : 0));
    printf("c blocked restarts      : %"PRIu64" (multiple: %"PRIu64") \n", solver.nbstopsrestarts,solver.nbstopsrestartssame);
    printf("c last block at restart : %"PRIu64"\n",solver.lastblockatrestart);
    printf("c nb ReduceDB           : %lld\n", solver.nbReduceDB);
    printf("c nb removed Clauses    : %lld\n",solver.nbRemovedClauses);
    printf("c nb learnts DL2        : %lld\n", solver.nbDL2);
    printf("c nb learnts size 2     : %lld\n", solver.nbBin);
    printf("c nb learnts size 1     : %lld\n", solver.nbUn);

    printf("c conflicts             : %-12"PRIu64"   (%.0f /sec)\n", solver.conflicts   , solver.conflicts   /cpu_time);
    printf("c decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, (float)solver.rnd_decisions*100 / (float)solver.decisions, solver.decisions   /cpu_time);
    printf("c propagations          : %-12"PRIu64"   (%.0f /sec)\n", solver.propagations, solver.propagations/cpu_time);
    printf("c conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", solver.tot_literals, (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
    printf("c nb reduced Clauses    : %lld\n",solver.nbReducedClauses);

    if (mem_used != 0) printf("c Memory used           : %.2f MB\n", mem_used);
    printf("c CPU time              : %g s\n", cpu_time);
}



static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
Cooperation * coop_ptr = NULL;
static void SIGINT_interrupt(int signum) {
    assert(coop_ptr != NULL);
    for(int i = 0 ; i < coop_ptr->nbThreads ; i++)
        coop_ptr->solvers[i].interrupt();
    coop_ptr->interrupted = true;
}


// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        printStats(*solver);
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); }

pthread_barrier_t barrier;
// Thread starter
void * startThread(void * in){

    int tId = *(int*) in;

    vec<Lit> dummy;
    assert(tId >= 0);
    assert(coop_ptr);
    assert(tId < coop_ptr->nbThreads);
    if(tId > 0){
        coop_ptr->solvers[0].cloneToSingle(& coop_ptr->solvers[tId]);
    }
    pthread_barrier_wait(&barrier);
    coop_ptr->solvers[tId].solveLimited(dummy);
    return NULL;
}

void getStatistics(int myRank){
    assert(coop_ptr);
    double sumOfReductionTimes = 0.0;
    
    
    long sumOfConflicts = 0;
    long sumOfDecisions = 0;
    long totalNumberExportedClauses = coop_ptr->nbClausesExported;
    long totalNumberExportedUnits   = coop_ptr->nbUnitsExported;
    long messagesSent               = coop_ptr->numMessagesSent;
    long bytesSent                  = coop_ptr->numBytesSent;
    long clauseLiftsTried       = 0L;
    long clauseLiftsSucc        = 0L;
    double print_sum = 0;
    
    for(int i = 0 ; i < coop_ptr->nbThreads ; i++){
        Solver & s          = coop_ptr->solvers[i];
        sumOfReductionTimes += s.sumOfReductionTimes;
        sumOfConflicts      += s.conflicts;
        sumOfDecisions      += s.decisions;
        clauseLiftsTried    += s.nbClausesExported;
        clauseLiftsSucc     += s.nbClausesLifted;
    }
    
    MPI_Reduce(&sumOfReductionTimes, &print_sum, 1, MPI_DOUBLE, MPI_SUM, 0, MPI_COMM_WORLD);
    
    long tmp;
    // Conflicts
    MPI_Reduce(&sumOfConflicts, &tmp, 1, MPI_LONG_LONG, MPI_SUM, 0, MPI_COMM_WORLD); if(myRank == 0) printf("c sum of conflicts: %ld\n", tmp);
    // Decisions:
    MPI_Reduce(&sumOfDecisions, &tmp, 1, MPI_LONG_LONG, MPI_SUM, 0, MPI_COMM_WORLD); if(myRank == 0) printf("c sum of decisions: %ld\n", tmp);
    // Number exported:
    MPI_Reduce(&totalNumberExportedClauses, &tmp, 1, MPI_LONG_LONG, MPI_SUM, 0, MPI_COMM_WORLD); if(myRank == 0) printf("c sum of exported clauses: %ld\n", tmp);
    // Number exported units:
    MPI_Reduce(&totalNumberExportedUnits, &tmp, 1, MPI_LONG_LONG, MPI_SUM, 0, MPI_COMM_WORLD); if(myRank == 0) printf("c sum of exported units: %ld\n", tmp);
    // Number of messages sent:
    MPI_Reduce(&messagesSent, &tmp, 1, MPI_LONG_LONG, MPI_SUM, 0, MPI_COMM_WORLD); if(myRank == 0) printf("c sent %ld messages via MPI\n", tmp);
    // Number of bytes sent:
    MPI_Reduce(&bytesSent, &tmp, 1, MPI_LONG_LONG, MPI_SUM, 0, MPI_COMM_WORLD); if(myRank == 0) printf("c sent %ld bytes via MPI\n", tmp);

    // Number of clause liftss tried:
    MPI_Reduce(&clauseLiftsTried, &tmp, 1, MPI_LONG_LONG, MPI_SUM, 0, MPI_COMM_WORLD); if(myRank == 0) printf("c tried %ld clause lifts\n", tmp);
    
    // Number of bytes sent:
    MPI_Reduce(&clauseLiftsSucc, &tmp, 1, MPI_LONG_LONG, MPI_SUM, 0, MPI_COMM_WORLD); if(myRank == 0) printf("c successfully lifted %ld clauses\n", tmp);
    
    
    if(myRank == 0){
        printf("c sum of reduction times: %lf\n", sumOfReductionTimes);
        
    }

}

void shutdownMPI(int myRank, int numSolvers){
    int othersRunning = numSolvers-1;
    for(int i = 0 ; i < numSolvers ; i++)
        if(i != myRank)
            MPI_Bsend(NULL, 0, MPI_INT, i, SHUTDOWN_TAG, MPI_COMM_WORLD);
    MPI_Status s;
    while(othersRunning > 0){
        // Receive something...
        MPI_Probe(MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &s);
        switch(s.MPI_TAG){
        case SHUTDOWN_TAG:
            MPI_Recv(NULL, 0, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
            othersRunning--;
            break;
        default:
            printf("c process %d received message with tag %d!\n", myRank, s.MPI_TAG);
            int * garbage;
            int length;
            MPI_Get_count(&s, MPI_INT, &length);
            garbage = (int*) malloc(length * sizeof(int));
            MPI_Recv(garbage, length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
        }
    }
}

//=================================================================================================
// Main:

int main(int argc, char** argv)
{

    try {
        //       printf("c\nc This is glucose 3.0 --  based on MiniSAT (Many thanks to MiniSAT team)\nc Simplification mode is turned on\nc\n");

        setUsageHelp("c USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");


#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        //printf("WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        BoolOption   mod   ("MAIN", "model",   "show model.", false);
        IntOption    vv  ("MAIN", "vv",   "Verbosity every vv conflicts", 10000, IntRange(1,INT32_MAX));
        BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", true);
        BoolOption   opt_cnc    ("MAIN", "cnc",    "Split the search space.", false);
        
        BoolOption   useMPI    ("MAIN", "useMPI",    "Use MPI processes.", true);
        BoolOption   uselazyImport    ("MAIN", "lazyImport",    "If a clause is unit on import, use one-watched scheme.", false);
        StringOption dimacs ("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    nbThreads("Parallel", "nbT","Num threads for each process.\n", 4, IntRange(1, 32));
        IntOption    opt_degree("Parallel", "degree","Maximum degree for each process in the communication graph.\n", 4, IntRange(0, 512));
        IntOption    opt_exchangePolicy("Parallel", "exportPolicy","Policy to export clauses: Fixed threshold(0), Dyanmic LBD/size threshold(1), Dynamic degree(2), lazy(3), fix degre(5), vivify before export(6).\n", 0, IntRange(0, 6));
        IntOption    opt_usageThreshold("Parallel", "usesBeforeSend","If using lazy clause exchange, how often does a clause have to be used locally before it is send\n", 1, IntRange(0, 32));
        // Options for clause exchange:
        // hard limit: max lbd
        IntOption    hardLimitLBD("Parallel", "maxLBD","Hard limit on LBD of clauses to exchange.\n", 5, IntRange(1, 32));
        // hard limit: size
        IntOption    hardLimitSize("Parallel", "maxSize","Hard limit on size of clauses to exchange.\n", 30, IntRange(1, 1024));
        // Interval between sending learnt clauses via MPI
        IntOption    cycleTime("Parallel", "cycleTime","Time between sending clauses via MPI in milliseconds.\n", 2000, IntRange(10, 100000));
        IntOption    targetExchange("Parallel", "targetExchange","Target of clauses to send per node per second.\n", 2000, IntRange(0, 100000));
        parseOptions(argc, argv, true);

        int numThreads = nbThreads;
        int myRank = 0;
        int numSolvers = 1;

        if(useMPI){
            MPI_Init(NULL, NULL);
            MPI_Comm_rank(MPI_COMM_WORLD, &myRank);
            MPI_Comm_size(MPI_COMM_WORLD, &numSolvers);

        }
        double tRunStart = MPI_Wtime();
        Cooperation coop(numThreads, 10, hardLimitLBD, hardLimitSize, useMPI, cycleTime, myRank, numSolvers);
        coop.exportPolicy=opt_exchangePolicy;
        coop.numNeighbours=opt_degree;
        coop.nbUsesBeforeSend = opt_usageThreshold;
        coop.target_exportClauses = targetExchange;
        coop.useCNC = opt_cnc;
        coop.oneWatchedImport = uselazyImport;

        ////////////////////////////////////////////
        // TODO
        // Set S to solver "0" from coop
        SimpSolver  &S = coop.solvers[0];

        // Set some options
        for(int i = 0 ; i < numThreads ; i++){
            coop.solvers[i].rnd_init_act = true;
            coop.solvers[i].random_seed += nbThreads*myRank + i;
        }
        double      initial_time = cpuTime();

        S.parsing = 1;
        if (!pre) S.eliminate(true);

        S.verbosity = verb;
        S.verbEveryConflicts = vv;
        S.showModel = mod;
        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

        // Set limit on CPU-time:
        double shutdownTime = MPI_Wtime() + (double) cpu_lim;

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("WARNING! Could not set resource limit: Virtual memory.\n");
            } }

        if (argc == 1)
            printf("Reading from standard input... Use '--help' for help.\n");

        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if (in == NULL)
            printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);

        if (S.verbosity > 0 && myRank == 0){
            printf("c ========================================[ Problem Statistics ]===========================================\n");
            printf("c |                                                                                                       |\n"); }


        parse_DIMACS(in, S);
        gzclose(in);

        if (S.verbosity > 0 && myRank == 0){
            printf("c |  Number of variables:  %12d                                                                   |\n", S.nVars());
            printf("c |  Number of clauses:    %12d                                                                   |\n", S.nClauses()); }

        double parsed_time = cpuTime();
        if (S.verbosity > 0 && myRank == 0){
            printf("c |  Parse time:           %12.2f s                                                                 |\n", parsed_time - initial_time);
            printf("c |                                                                                                       |\n"); }

        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        signal(SIGINT, SIGINT_interrupt);
        signal(SIGXCPU,SIGINT_interrupt);

        S.parsing = 0;
        S.eliminate(true);
        double simplified_time = cpuTime();
        if (S.verbosity > 0 && myRank == 0){
            printf("c |  Simplification time:  %12.2f s                                                                 |\n", simplified_time - parsed_time);
            printf("c |                                                                                                       |\n"); }

        if (!S.okay()){
            if (S.certifiedUNSAT) fprintf(S.certifiedOutput, "0\n"), fclose(S.certifiedOutput);
            //if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            if (S.verbosity > 0){
                printf("c =========================================================================================================\n");
                printf("Solved by simplification\n");
                printStats(S);
                printf("\n"); }
            printf("s UNSATISFIABLE\n");
            exit(20);
        }

        if (dimacs){
            if (S.verbosity > 0)
                printf("c =======================================[ Writing DIMACS ]===============================================\n");
            S.toDimacs((const char*)dimacs);
            if (S.verbosity > 0)
                printStats(S);
            exit(0);
        }

        ////////////////////////////////////////////
        // CHECK
        // Initialise all the solvers
        coop.adjustNumThreads(numThreads, mem_lim);
        if(coop.nbThreads != numThreads){
            assert(coop.nbThreads < numThreads);
            numThreads = coop.nbThreads;
            printf("c adjusting number of threads to %d\n", numThreads);
        }

        for(int i = 0 ; i < numThreads ; i++){
            // Set parameters
            coop.solvers[i].use_simplification = false;
            coop.solvers[i].threadId = i;
            coop.solvers[i].procId = myRank;
            coop.solvers[i].numProcesses = numSolvers;
            coop.solvers[i].verbosity = 2;
            coop.solvers[i].verbEveryConflicts = vv;
            coop.solvers[i].verbosity = verb;
            coop.solvers[i].showModel = mod;
            coop.solvers[i].deterministic_mode = 0;
            coop.solvers[i].runningCnC= false;
            assert(coop.solverStates);
            assert(coop.cubePending);
        }

        // Create and attach MPI buffer
        if(useMPI){
            int buf_size = 100 * 1000 * 1000 * sizeof(int);
            int * my_buffer = (int*) malloc(buf_size);
            assert(my_buffer);
            MPI_Buffer_attach(my_buffer, buf_size);
        }

        // Start the threads
        pthread_t threads[numThreads];
        int ids[numThreads];
        pthread_barrier_init(&barrier, NULL, numThreads);
        coop_ptr = &coop;
        for(int i = 0 ; i < numThreads ; i++){
            ids[i] = i;
            pthread_create(&threads[i], NULL, startThread, &ids[i]);
        }

        coop.communicationThread(shutdownTime);
#ifdef GLOBAL_DEBUG
        printf("c com-thread of process %d terminated, not waiting for the solver threads! \n", myRank);
#endif

        // Join the threads
        for(int i = 0 ; i < numThreads ; i++){
            int join_ret = pthread_join(threads[i], NULL);
            assert(join_ret == 0);
        }
        int totalNumberExportedClauses = 0;
        int totalNumberLiftedClauses = 0;
        int totalNumberLearntClauses = 0;
        for(int i = 0 ; i < numThreads ; i++){
            totalNumberExportedClauses += coop.clausesSent[i];
            totalNumberLiftedClauses += coop.clausesLifted[i];
            totalNumberLearntClauses += coop.conflicts[i];
        }
        if(opt_exchangePolicy == EXPORT_VIVIFY_BEFORE){
            printf("c process %d : lifted %d of %d exported clauses, total learnt: %d\n", myRank, totalNumberLiftedClauses, totalNumberExportedClauses, totalNumberLearntClauses);
        }
        printf("c process %d: Joined all threads\n", myRank);

        // Get the result

        lbool ret = l_Undef;
        for(int i = 0 ; i < numThreads ; i++){
            if(coop.answers[i] != l_Undef){
                assert(ret == l_Undef || ret == coop.answers[i]);
                ret = coop.answers[i];
            }
        }
        bool printResult = !useMPI;
        printf("c this is process %d. mod=%d, useMPI=%d, global result %c my result %c\n", myRank, mod ? 1 : 0, useMPI? 1 : 0, coop.globalResult == l_True ? '1' : (coop.globalResult == l_False ? '0' : '?'), ret == l_True ? '1' : (ret == l_False ? '0' : '?'));
        // If MPI is used AND the result is true AND we want to print the result - decide who does it!
        if(mod && useMPI && mod && (ret == l_True || coop.globalResult == l_True)){
            int myOffer = ret == l_True ? myRank : numSolvers+1;
            // MPI_Reduce(&clauseLiftsSucc, &tmp, 1, MPI_LONG_LONG, MPI_SUM, 0, MPI_COMM_WORLD); if(myRank == 0) printf("c successfully lifted %ld clauses\n", tmp);
            int chosen;
            MPI_Allreduce(&myOffer, &chosen, 1, MPI_INT, MPI_MIN, MPI_COMM_WORLD);
            if(chosen == myRank){
                printf("c process %d chosen to write the result! \n", myRank);
                printResult = true;
            }
        }
        if(ret == l_True && mod && printResult){
            coop.solvers[0].extendModel();
        }
        if (S.verbosity > 0 && myRank == 0){
            printStats(S);
             }

        if(!useMPI || myRank == 0){
            if(ret == l_Undef)
                ret = coop.globalResult;
            printf(ret == l_True ? "s SATISFIABLE\n" : ret == l_False ? "s UNSATISFIABLE\n" : "s INDETERMINATE\n");
        }
        FILE* res = NULL;
        if(S.showModel && ret == l_True && printResult)
            res = (argc >= 3) ? fopen(argv[argc-1], "wb") : NULL;
        if (res != NULL){
            if (S.showModel && ret == l_True && printResult){
                //printf("SAT\n");
                fprintf(res, "v ");
                for (int i = 0; i < S.nVars(); i++){
                    assert(S.model[i] != l_Undef);
                    if (S.model[i] != l_Undef)
                        fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
                }
                fprintf(res, " 0\n");
                fclose(res);
            }

        } else {
            if(S.showModel && ret==l_True && printResult) { // TODO: Assert that value is not UNDEF!
                printf("v ");
                for (int i = 0; i < S.nVars(); i++)
                    if (S.model[i] != l_Undef)
                        printf("%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
                    else
                        assert(false && "Variable value is undefined! ");
                printf(" 0\n");
            }

        }
        if(useMPI){

#ifdef GLOBAL_DEBUG
            double tStart = MPI_Wtime();
            printf("c process %d at barrier\n", myRank);
#endif
            MPI_Barrier(MPI_COMM_WORLD);
            // Gather some statiscits here:
            getStatistics(myRank);
#ifdef GLOBAL_DEBUG
            printf("c process %d passed barrier\n", myRank);
#endif
            shutdownMPI(myRank, numSolvers);
#ifdef GLOBAL_DEBUG
            printf("c process %d finished the shutdown routine! \n", myRank);
#endif

            if(myRank == 0)
                printf("c time till here: %lf mem %lf maxMem %lf\n",MPI_Wtime()- tRunStart, memUsed(), memUsedPeak());
            MPI_Finalize();
#ifdef GLOBAL_DEBUG
            double t_before_finalize = MPI_Wtime();
            printf("c MPI_Finalize is done for process %d , all this stuff took %lf seconds! \n", myRank, t_before_finalize-tStart);
#endif

        }
        exit(0);
#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
        printf("c =========================================================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
