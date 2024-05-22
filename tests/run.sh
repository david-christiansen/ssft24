#!/usr/bin/env bash

cd "$(dirname "$0")" || exit 1

mkdir -p out expected

bobfilter="lake -d=.. exe bobfilter"

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
    $bobfilter "$(<"$t")" < input.json > "expected/$t"
    echo
  else
    if $bobfilter "$(<"$t")" < input.json > "out/$t"
    then
      if diff -Nu "expected/$t" "out/$t" > "out/$t.diff"
      then
        echo "✅"
       else
        failed+=("$t")
        echo "❌"
        cat "out/$t.diff"
      fi
    else
      failed+=("$t")
      echo "❌"
    fi
  fi
done

if (( ${#failed[@]} )); then
  echo "Some tests failed. Rerun with"
  echo "$0 ${failed[*]}"
  exit 1
fi
