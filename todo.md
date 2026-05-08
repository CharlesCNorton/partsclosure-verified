# TODO

- Replace `Part = nat` with a `Module Type` parameter over a decidable carrier so real SKUs can be plugged in without renumbering.
- Add `NoDup` invariants and prove closures equal up to `Permutation`, not just list equality.
- Add the dual operator: least closed superset of a target set, computed as a least fixed point. This answers "what is the minimum bootstrap kit that can build T?" (the user-facing question the repo description implies).
- Add multiset quantities to recipes. Prove producibility as a supply-meets-demand constraint with conservation, not as a pure set-membership check.
- Expose the recipe dependency graph explicitly. Prove the closure equals the union of strongly-connected components reachable from zero-input recipes.
- Set up `Extraction` to OCaml so the closure operator runs against a real catalog file.
- Replace the 7-part toy example with a real industrial BoM (open-source 3D printer, Linux laptop, lathe, etc.) and produce a verified closure result.
