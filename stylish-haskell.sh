#!/bin/bash
for file in $(find src test examples -name '*.hs');
do
    diff $file <(stylish-haskell $file);
done;
