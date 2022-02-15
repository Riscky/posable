#!/bin/bash
for file in $(find . -name '*.hs');
do
    diff $file <(stylish-haskell $file);
done;
