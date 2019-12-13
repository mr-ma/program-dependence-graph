
shouldskip=$2
skip=true
if [ -z "$shouldskip" ]
then
      skip=false
fi
datasets=$1/*
for ds in $datasets
do
  if $skip ; then
    echo 'Skipping if files exist!'
    if [ -f $ds/blocks.csv ]; then
      echo "Found $ds/blocks.csv"
      continue
    fi
  else 
    #rm $ds/relations.csv $ds/blocks.csv
    if [ -f $ds/blocks.csv ]; then
      echo "No skip so I want to remove $ds/blocks.csv and $ds/relation.csv"
      exit 1
    fi
  fi
  #CONT=0
  #{
   #flock -x 200
   if [ -d "$ds/process" ]; then
      echo "Skipping in process $ds"
      CONT=1
   else
      mkdir -p "$ds/process"
   fi

  #}200>/var/lock/csvgenerator

  bc_files=$ds/*.bc
  for bc in $bc_files
  do
    filename=${bc##*/}
    echo "handing $filename"
    opt-7 -load /home/sip/program-dependence-graph/build/libpdg.so -reg2mem -pdg-csv -append -relations "$ds/relations.csv" -blocks "$ds/blocks.csv" $bc
    #opt-7 -load /home/sip/program-dependence-graph/build/libpdg.so -reg2mem -pdg-csv -append -relations "relations.csv" -blocks "blocks.csv" $bc
    retVal=$?
    if [ $retVal -ne 0 ]; then
      echo "Error"
      exit 1
    fi
  done
  rm -r "$ds/process"
done
