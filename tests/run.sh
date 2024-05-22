#!/usr/bin/env bash

cd "$(dirname "$0")" || exit 1

mkdir -p out expected

jsonfilter="lake -d=.. exe jsonfilter"

if [ "$1" = "-a" ]
then
  shift
  accept=true
fi

tests=""
if [ $# -eq 0 ]
then
  tests=(query*.json)
else
  tests=( "$@" )
fi

failed=()

for t in "${tests[@]}"
do
  echo -n "Running $t... "
  if [ "$accept" = true ]
  then
    $jsonfilter "$(<"$t")" < input.json > "expected/$t"
    echo
  else
    if $jsonfilter "$(<"$t")" < input.json > "out/$t"
    then
      if diff -Nu "expected/$t" "out/$t" > "out/$t.diff"
      then
        echo "✅ $t"
       else
        failed+=("$t")
        echo "❌"
        cat "out/$t.diff"
      fi
    else
      failed+=("$t")
      echo "❌ $t"
    fi
  fi
done

if (( ${#failed[@]} )); then
  echo "Some tests failed. Rerun with"
  echo "$0 ${failed[*]}"
  exit 1
fi
