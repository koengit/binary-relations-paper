#!/bin/bash

for i in E Spass CVC4 Z3 Vampire ;  do
	for j in PEqualified Transified Equalified ; do
#		for k in subset_notransaxiom ; do

#			comm -23 $j $k 


cd ~/Documents/binary-relations-paper/Plots/${j}/${i}
./getValues.sh original_${i} ${j}_${i}
	
#./intersect.sh Transified_$i $j > temp
#VAR=$(./go.sh  original_$i temp | wc -l) # original best
#VAR2=$(./go.sh  temp original_$i  | wc -l) # transformed best
#VAR3=$(./go.sh temp original_$i | fgrep 1.0 )
#echo $i $j $VAR $VAR2 $VAR3
done
done
