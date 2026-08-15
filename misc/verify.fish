#!/usr/bin/env fish

set target $argv[1]
printf "%s\n" $target

splr -c $target

switch $status
    case 10
        echo "sat"
        dmcr $target
        echo $status
        if test $status -eq 0
            echo "✅ $target"
        else
            echo "❌ $target"
        end
    case 20
        echo "unsat"
        drat-trim $target proof.drat
        if test $status -eq 0
            echo "✅ $target"
        else
            echo "❌ $target"
        end
    case 124
        echo "timeout"
    default
        echo "unknown return value"
end
