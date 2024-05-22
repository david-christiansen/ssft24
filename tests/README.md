A simple test suite
-------------------

This test suite applies the queries defined in `query*.json` to the input in
`input.json`, and compares them against the expected output in `expected/`.

Usage:

```
./run.sh                                  # runs all tests
./run.sh query_any.json query_2024.json   # runs selective tests
./run.sh -a                               # accepts the current output
```
