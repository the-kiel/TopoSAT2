if [ ! -e bin ] ; then 
	mkdir bin
fi
currDir=$(pwd)
cd simp && make clean && make
cp glucose $currDir/bin
