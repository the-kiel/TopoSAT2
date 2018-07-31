/************************************************************************************[Constants.h]
 Glucose -- Copyright (c) 2009, Gilles Audemard, Laurent Simon
                CRIL - Univ. Artois, France
                LRI  - Univ. Paris Sud, France
  
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

#define DYNAMICNBLEVEL
#define CONSTANTREMOVECLAUSE
#define UPDATEVARACTIVITY

// Constants for clauses reductions
#define RATIOREMOVECLAUSES 2



// Constants for restarts
#define LOWER_BOUND_FOR_BLOCKING_RESTART 10000

#define RESTART_LUBY                    0x1
#define RESTART_INNER_OUTER             0x3
#define RESTART_GLUCOSE_DEFAULT         0x10


// Possible return values of clause minimisation
#define FORMULA_UNSAT                   0x1
#define SHRINKED                        0x2
#define CONFLICT                        0x3
#define SATISFIED                       0x4
#define NO_REDUCE                       0x5

// Size of a clause header: 
// - size
// - LBD
// - id of learning thread
// - respective id of the clause 

#define SIZE_CLAUSE_HEADER              4

//#define GLOBAL_DEBUG
