List of things that should or could be done:

- Make rvconcat a semigroup instance
- Simplify ZipWith' (<>) (since we don't use the higher-orderness of ZipWith anyway)
- Simplify our MemRep BaseType instances with overlapping instances (if possible)
- Check Finite's on compile time (probably need some reification there)
- Write more (all) generic GMemRep instances
- Write the proposal :)
- Add a linter
- Add some tests (quickcheck)
- Clean up the generic helper functions
- Fix up finites and indexing with constraints
- PR@finite to let `finite` understand the class of `Integral`s instead of just `Integer`s
- Remove Nix stuff and use Stack (hard to get things linked locally otherwise)
- Convert back to original representation
