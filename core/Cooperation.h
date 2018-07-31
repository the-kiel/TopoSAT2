/*****************************************************************************************[Cooperation.h]
Copyright (c) 2008-20011, Youssef Hamadi, Saïd Jabbour and Lakhdar Saïs

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
*******************************************************************************************/

#include "core/SolverTypes.h"
#include "core/Solver.h"
#include "simp/SimpSolver.h"
#include "utils/System.h"
#include <pthread.h>

#include <vector>
#include <algorithm>
#include <map>
#include <list>
//#include "Determanager.h"


namespace Glucose {

//=================================================================================================
// Options:

#define MAX_EXTRA_CLAUSES     200000
#define MAX_EXTRA_UNITS       20000
#define USAGE_BUFFER_SIZE       20000

#define MAX_IMPORT_CLAUSES    4000
#define LIMIT_CONFLICTS_EVAL  6000

#define INITIAL_DET_FREQUENCE 700

#define AIMDX  0.25
#define AIMDY  8

// FLAGS for MPI communication
#define LEARNT_CLAUSE_TAG 1
#define REPORT_TAG        2
#define SHUTDOWN_TAG      3
    
#define NEW_CUBES_FOR_MASTER_TAG            101         // Slave sends new cubes to master process
#define NEW_CUBE_FOR_SLAVE_TAG              102         // Master process sends new cubes to slave 
#define CUBE_FAILED_TAG                     103         // Slave notifies master that a cube was solved w/o solution
#define NEW_FREE_SLAVE_TAG                  104  
#define STEAL_WORK_TAG                      105
   
#define EXPORT_FIX_THRESHOLD                                    0
#define EXPORT_DYNAMIC_THRESHOLD                                1
#define EXPORT_DYNAMIC_DEGREE                                   2
#define EXPORT_LAZY_EXCHANGE                                    3
#define EXPORT_DYNAMIC_THRESHOLD_DEGREE_INDEPENDET              4   
#define EXPORT_FIX_DEGREE_FIX_THRESHOLD                         5    
#define EXPORT_VIVIFY_BEFORE                                    6
    
    
#define SOLVER_STATE_PORTFOLIO                                  100
#define SOLVER_STATE_CNC                                        101
    
#define USE_BIG_STUFF               (false)

/*=================================================================================================
 Cooperation Class : ->  [class]
Description:
	This class manage clause sharing component between threads,i.e.,
	It controls read and write operations in extraUnits and extraClauses arrays
    iterators headExtra... and tailExtra... are used to to this end
=================================================================================================*/

  class Cooperation{

  public:

    bool		start, end;				// start and end multi-threads search
    int			nbThreads;				// numbe of  threads
    int         nbBuffers;
    int			limitExportClauses;			// initial limit size of shared clauses
    //double**	        pairwiseLimitExportClauses;		// pairwised limit limit size clause sharing

    SimpSolver*		solvers;				// set of running CDCL algorithms
    lbool*		answers;				// answer of threads
    lbool       globalResult;     // Result either found locally, or received via MPI
    
    
    Lit**       extraUnitInBuffers_solvers; // Each solver has one in-buffer for unit clauses. Only the communication thread writes to these buffers
    Lit**       extraUnitInBuffer_comThread; // The comm-thread has one in-slot for every solver thread, where unit clauses are written to 
//     Lit***		extraUnits;				// where are stored the shared unit clauses
    int*		headExtraUnits_solvers;
    int*		tailExtraUnits_solvers;
     int*		headExtraUnits_comThread;
    int*		tailExtraUnits_comThread;

    Lit****		extraClauses;				// where are stored the set of shared clauses with size > 1
    int**		headExtraClauses;
    int**		tailExtraClauses;

    int**               usedMessages;
    int**               deletedMessages;
    int*                headUsedMessages;
    int*                tailUsedMessages;
    int*                headDeletedMessages;
    int*                tailDeletedMessages;

    
    // Logging of clause usages: 
     std::map<std::pair<int, int>, int> clausesUsed;
    std::map<std::pair<int, int>, int> clausesDeleted;
    std::map<std::pair<int, int>, std::vector<int> > lazyClauseStorage;
    std::vector<std::set<int> > unitsReceivedFrom;
    // MPI stuff
    std::vector<Lit> MPI_out_queue_units;
    std::vector<std::vector<int> > MPI_out_queue_clauses;
    lbool mpi_communication();
    void dispatchReceivedClauses();
    void MPI_exportUnitClause(Lit l);
    void MPI_store_export_clause(vec<Lit>& learnt, int lbd);
    void MPI_send_data(double currentProductionRate);
    void handleReceivedClauses(int * recvData, int length);
    void storeInBIG(Lit l1, Lit l2);
    bool rejectByBIG(Lit l1, Lit l2);
    void getNumStoredClauses(int i, int & m, int & s);
    void send_wrapper(void * data, int num, MPI_Datatype d, int dest, int tag, MPI_Comm c);
    
    //---------------------------------------
    int                 initFreq;                               // barrier synchronization limit conflicts in deterministic case
    int*                deterministic_freq;                     // in dynamic case, #conflicts barrier synchronization
    int*		nbImportedExtraUnits;                   // counters fot the total imported Unit clauses
    int*		nbImportedExtraClauses;			// counters fot the total imported Extra clauses
    uint64_t*           learntsz;
    char		ctrl;					// activate control clause sharing size mode
    double		aimdx, aimdy;				// aimd control approach {aimdx, aimdy are their parameters}
    //int**		pairwiseImportedExtraClauses;		// imported clause of for and from each thread
    bool		deterministic_mode;			// running Minisat in deterministic mode

    vec<lbool> shared_model;
    pthread_mutex_t model_semaphore;

    int hard_limit_lbd;
    int hard_limit_size;

    int factor_lbd;
    int factor_size;
    int weightedExportLimit;
    int exportPolicy;
    int numNeighbours;
    int comCycleTime;
    int nbUsesBeforeSend;
    bool useMPI;
    bool oneWatchedImport;      // If a clause was unit, import it as one-watched rather than backtracking!
    bool interrupted;
    int procId;
    int numProcesses;
    int target_exportClauses;           // Target: How many clauses should be exported in each com cycle?
    // TODO: Vector of adjacent processes?
    std::set<int> units_send; 	// units known outside
    bool 	forward_units;
    void communicationThread(double shutdown_time);
    int readInternalBuffer();           /* Returns how many clauses have been found in the internal buffer */
    lbool readIncomingMessages();
    void storeReceivedClause(Lit * l);
    void storeClauseInMPIBuffer(Lit * l);
    void handleNewUnit(Lit l, bool fromInside);
    void lazyStoreClauses(Lit * l);
    lbool checkStatus();
    void updateThreshold(int recvInternal, double timeSinceLastUpdate);
    
    
    /*
     * Some statistics: 
     * 
     * */
    int numClausesSent;
    int numClausesReceived;
    int numLiteralsSent;
    std::vector<int> clausesSent;
    std::vector<int> clausesLifted;
    std::vector<int> conflicts;
    
    /********************************************************************************
     * Some things for Cube&Conquer-Mode
     * */
    
    bool useCNC;
    std::list<std::vector<int> > master_OpenJobs;
    std::list<int> freeSlaves;
    int threadsRunningCnC;
    std::vector<int> progress;
    
    pthread_mutex_t cube_lock;
    int  *  solverStates;
    bool *  cubePending;
    bool *  stealRequestPending;
    std::vector<std::vector<int> > newCubesForMaster, newCubesForSlave;
    std::vector<std::pair<int, int> > notificationFailedCubes; // Tuple (threadId, cubeLength)
    std::vector<int> newFreeSlaves;
    
    
    // Master->Slave: New cube to solve
    void sendNewCube(int targetId, std::vector<int> & cube);
    // Slave->Master: Result of working on cube
    void receiveCubeResult();
    
    void master_organize_cnc(double & time_last_steal);
    void master_receive_new_cubes(MPI_Status & s);
    bool master_receive_failed_cube(MPI_Status & s);
    void comForwardCubes(MPI_Status & s);
    void master_newFreeSlave(MPI_Status & s);
     int getThreadIndex(int procNo, int threadNo) { return numProcesses*threadNo + procNo; }
     int getNumSolverThreads() { return numProcesses * nbThreads; }
    int getProcId(int threadIndex){ return threadIndex % numProcesses; }
    int getLocalThreadId(int threadIndex) { return threadIndex / numProcesses; }
    void manageCubeConquer();
    void readCubeConquerBuffers();
    
    //=================================================================================================

    std::set<int> knownUnits;
    int unitsReceived;
    
    bool exportExtraUnit		(int id, Lit unit);
    void importExtraUnits		(Solver* s);
    void importExtraUnits		(Solver* s, vec<Lit>& lits);

    void exportExtraClause		(int id, vec<Lit>& learnt, int lbd, int threadId, int index);
    void exportExtraClause		(int id, Clause& c, int threadId, int index);
    void importExtraClauses		(Solver* s);

    void addExtraClause			(Solver* s, int t, Lit* lt);
    void addExtraClause1		(Solver* s, int t, Lit* lt);
    void addExtraClause2		(Solver* s, int t, Lit* lt);

    void uncheckedEnqueue               (Solver* s, int t, Lit l);
    void storeExtraUnits                (Solver* s, int t, Lit l, vec<Lit>& lits);

    
    void clauseDeleted                  (int sender, int origin, int index);
    void clauseUsed                     (int sender, int origin, int index);
    
    
    int readUsageBuffers               ();
    void readDeletedBuffers               ();
    
    int clauseUsed                     (int origin, int index);
    
    void printUsageStats                ();
    void adjustNumThreads               (int maxThreads, int maxMem);
    //---------------------------------------
    //void updateLimitExportClauses       (Solver* s);

    void printStats			(int& id);
    //void printExMatrix			();
    void Parallel_Info			();
    
    long nbClausesExported;
    long nbUnitsExported;
    long nbLiteralsExported;
    int numMessagesSent;
    long numBytesSent;
    
   
    //=================================================================================================
    inline int nThreads      ()			{return nbThreads;		}
    inline int limitszClauses()			{return limitExportClauses;	}
    inline lbool answer      (int t)		{return answers[t];		}
    inline bool setAnswer    (int id, lbool lb) {answers[id] = lb; return true;	}

    //=================================================================================================
    // Constructor / Destructor

    Cooperation(int n, int l, int maxLBD, int maxSize, bool _useMPI, int cycleTime, int _procId, int _numProcesses){
        interrupted = false;
      useMPI = _useMPI;
      procId = _procId;
      numProcesses = _numProcesses;
      comCycleTime = cycleTime;
      hard_limit_lbd = maxLBD;
      hard_limit_size = maxSize;
      factor_lbd = 100;
      factor_size = 1;
      weightedExportLimit = 400;
      target_exportClauses = 1000;
      pthread_mutex_init(&model_semaphore, NULL);
      limitExportClauses = l;
      nbThreads	= n;
      clausesSent.resize(nbThreads, 0);
      clausesLifted.resize(nbThreads, 0);
      conflicts.resize(nbThreads, 0);
      nbBuffers = nbThreads+1;
      globalResult = l_Undef;
      end         = false;
      numClausesReceived = 0;
      numClausesSent = 0;
      numLiteralsSent = 0;
      nbUsesBeforeSend = 1;
      
      
    nbClausesExported       = 0L;
    nbUnitsExported         = 0L;
    nbLiteralsExported      = 0L;
    numMessagesSent         = 0;
    numBytesSent            = 0L;
      
      solvers	            = new SimpSolver    [nbThreads];
      answers	            = new lbool     [nbBuffers];
      assert(answers);

      extraUnitInBuffers_solvers            = new Lit*     [nbBuffers];
      extraUnitInBuffer_comThread            = new Lit*     [nbBuffers];
      headExtraUnits_solvers        = new int      [nbBuffers];
      tailExtraUnits_solvers        = new int      [nbBuffers];
      headExtraUnits_comThread        = new int      [nbBuffers];
      tailExtraUnits_comThread        = new int      [nbBuffers];

      extraClauses          = new Lit***    [nbBuffers];
      headExtraClauses      = new int*      [nbBuffers];
      tailExtraClauses      = new int*      [nbBuffers];
      
      headUsedMessages      = new int [nbBuffers];
      tailUsedMessages      = new int [nbBuffers];
      usedMessages          = new int* [nbBuffers];
      headDeletedMessages      = new int [nbBuffers];
      tailDeletedMessages      = new int [nbBuffers];
      deletedMessages       = new int* [nbBuffers];
      
      
      /*************************************************************
       *  Stuff for cube exchange: 
       * */
      solverStates = new int[nbThreads * numProcesses];
      assert(solverStates);
//       printf("c initialising cubePending for %d threads! \n", nbThreads);
      cubePending = new bool[nbThreads];
      stealRequestPending = new bool[nbThreads];
      assert(cubePending);
      newCubesForSlave.resize(nbThreads);
      threadsRunningCnC=0;
      pthread_mutex_init(&cube_lock, NULL);
      for(int i = 0 ; i < nbThreads ; i++){
          cubePending[i] = false;
          stealRequestPending[i] = false;
          for(int j = 0 ; j < numProcesses ; j++){
              solverStates[getThreadIndex(j, i)]=SOLVER_STATE_PORTFOLIO;
              if(i <= nbThreads/2)
                freeSlaves.push_back(getThreadIndex(j, i));
          }
      }
      
      for(int t = 0; t < nbBuffers; t++){
          if(t < nbThreads)
            solvers[t].coop = this;
// 	extraUnits	  [t]    = new Lit* [nbBuffers];
          extraUnitInBuffers_solvers[t] = new Lit[MAX_EXTRA_UNITS];
          headExtraUnits_solvers[t] = 0;
          tailExtraUnits_solvers[t] = 0;
          extraUnitInBuffer_comThread[t] = new Lit[MAX_EXTRA_UNITS];
          headExtraUnits_comThread[t] = 0;
          tailExtraUnits_comThread[t] = 0;
// 	headExtraUnits	  [t]    = new int  [nbBuffers];
// 	tailExtraUnits	  [t]    = new int  [nbBuffers];

	extraClauses	  [t]    = new Lit**[nbBuffers];
	headExtraClauses  [t]    = new int  [nbBuffers];
	tailExtraClauses  [t]    = new int  [nbBuffers];

        headUsedMessages[t] = 0;
        tailUsedMessages[t] = 0;
        usedMessages[t] = new int[USAGE_BUFFER_SIZE];
        headDeletedMessages[t] = 0;
        tailDeletedMessages[t] = 0;
        deletedMessages[t] = new int[USAGE_BUFFER_SIZE];
        
	for(int k = 0; k < nbBuffers; k++){
// 	  extraUnits	  [t][k] = new Lit  [MAX_EXTRA_UNITS];

// 	  headExtraUnits  [t][k] = 0;
// 	  tailExtraUnits  [t][k] = 0;

	  extraClauses	  [t][k] = new Lit* [MAX_EXTRA_CLAUSES];
	  headExtraClauses[t][k] = 0;
	  tailExtraClauses[t][k] = 0;
	}
      }

      //=================================================================================================
      aimdx    = AIMDX;
      aimdy    = AIMDY;
      initFreq = INITIAL_DET_FREQUENCE;
      deterministic_mode = false;

      learntsz                    = new uint64_t[nbBuffers];
      deterministic_freq          = new int     [nbBuffers];
      nbImportedExtraClauses      = new int	[nbBuffers];
      nbImportedExtraUnits        = new int	[nbBuffers];
      //pairwiseImportedExtraClauses= new int*	[nbBuffers];
      //pairwiseLimitExportClauses  = new double*	[nbBuffers];

      for(int t = 0; t < nbBuffers; t++){
	learntsz              [t] = 0;
	answers               [t] = l_Undef;
	deterministic_freq    [t] = initFreq;
	nbImportedExtraClauses[t] = 0;
	nbImportedExtraUnits  [t] = 0;

	//pairwiseImportedExtraClauses [t]= new int   [nbBuffers];
	//pairwiseLimitExportClauses   [t]= new double[nbBuffers];

	//for(int k = 0; k < nbBuffers; k++)
	 // pairwiseLimitExportClauses[t][k]= l;

      }
    }
    //=================================================================================================
    ~Cooperation(){}
  };
}
