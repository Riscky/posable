List of things that should or could be done:

- Make rvconcat a semigroup instance
- Simplify ZipWith' (<>) (since we don't use the higher-orderness of ZipWith anyway)
- And maybe do away with Eval (and Fcf) completely
- Split MemRep into modules and remove the sillyness in Main
- Write an instance for Mult
- Make a higher order version of zipLeft, zipRight and rnsConcat
- Choose a better append operator for RNS
- Figure out how overlapping instances work and simplify our MemRep BaseType instances (and maybe IsRNS)
