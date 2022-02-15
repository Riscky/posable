#!/bin/bash
for file in $(find src -name '*.hs');
do
    diff $file <(stylish-haskell $file);
done;
