#!/bin/sh -norc

UUF250=$1
echo ${UUF250}

for f in ${UUF250}/*.cnf; do
    target=`basename -s .cnf $f`
    echo "########################################"
    echo "# ${target}.cnf"
    rm -f ${target}.out
    splr -c -p ${target}.out ${f} > /dev/null
    if [ -z ${target}.out ]; then
        echo ' FAIL TO CERTIFICATE: ${f}'
        exit 1;
    fi
    egrep -v '^[cs]' < ${target}.out > ${target}.drat
    gratgen ${f} ${target}.drat -o ${target}.grad -j 4 > /dev/null
    gratchk unsat ${f} ${target}.grad
done
