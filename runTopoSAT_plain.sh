# write output and result (if SAT) to two files
resultFile="RES$$.txt"
tmpFile="tmp$$.txt"
errorFile="err$$.txt"

mpirun -np 1 bin/glucose -cpu-lim=5000 -nbT=24 -mem-lim=64000 -restartPortfolio -model -maxLBD=4 -exportPolicy=6 $1 $resultFile > $tmpFile 2>$errorFile
# write answer
grep "^s " $tmpFile
# if sat, write satisfying assignment
if [ -e $resultFile ] ; then
    cat $resultFile
    rm $resultFile
fi

# clean up
rm $tmpFile
rm $errorFile
