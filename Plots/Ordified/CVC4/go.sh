#!/bin/bash
set_intersect() {
    comm -12 <(for x in $1; do basename $x; done | sort) <(for x in $2; do basename $x; done | sort)
}


list1=$(awk '{ if ($2 == "success" ) { print $1; } }' $1)
list2=$(awk '{ if ($2 == "fail" ) { print $1; } }' $2)
diff=$(set_intersect "$list2" "$list1")

for i in $diff; do
    echo $(basename $i) $(awk '{ if ($2 == "Rating") { print $4; } }' $TPTP/Problems/*/$(basename $i))
done 
