List of things that should or could be done:

- Make rvconcat a semigroup instance
- Simplify ZipWith' (<>) (since we don't use the higher-orderness of ZipWith anyway)
- And maybe do away with Eval (and Fcf) completely
- Split MemRep into modules
- Make a higher order version of zipLeft, zipRight and rnsConcat
- Choose a better append operator for RNS
- Figure out how overlapping instances work and simplify our MemRep BaseType instances (and maybe IsRNS)
- Rewrite widths to a function over a MemRep instead of a function in the class itself
- Check Finite's on compile time (probably need some reification there)
- Write more generic GMemRep instances
- Write the proposal :)
