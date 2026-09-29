-- Prove2me | Definitions.Def_Applications_GraphTheory_RandomRecursiveTree
-- name    : Applications_GraphTheory_RandomRecursiveTree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:46:34.882038+00:00
-- url     : https://prove2.me/theorems/ca3276ef-d91d-440b-bd34-d5e1ca5f2b37
-- title:
--   Aether Catalog definitions — Applications_GraphTheory_RandomRecursiveTree
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.GraphTheory.RandomRecursiveTree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/GraphTheory/RandomRecursiveTree.lean by skeleton subtraction
import Mathlib

/-!
# The `d = 1` case: random recursive trees

The descendant limit law for random recursive `d`-DAGs specialises, at `d = 1`, to the
classical random recursive tree (Drmota, 2009).  Here the mean-growth product
`P_n(a) = ∏_{k=1}^n (1 + a/k)` is taken with `a = 1`, and it degenerates to a strikingly
simple closed form.

The main results are:

* `descProductOne_eq` : the exact identity `P_n(1) = n + 1`, so the expected number of
  descendants grows **linearly** in `n` (in contrast to the `n^{1/d}` growth for
  `d ≥ 2`);
* `descProductOne_div_tendsto` : consequently `P_n(1) / n ⟶ 1`, i.e. the scaling
  exponent is exactly `1`, the `d = 1` value of `1/d`.

The product is defined here independently so that this file is self-contained.
-/

open Real Filter Topology

namespace DDAG

/-- The mean-growth product `P_n(a) = ∏_{k=1}^n (1 + a/k)` (repeated here so the file is
self-contained). -/
noncomputable def rrtProduct (a : ℝ) (n : ℕ) : ℝ := ∏ k ∈ Finset.Icc 1 n, (1 + a / (k : ℝ))

/-
**Closed form at `a = 1`.** For the random recursive tree, `P_n(1) = n + 1`.
-/

/-
**Linear scaling of descendants for `d = 1`.** `P_n(1) / n ⟶ 1`, so the scaling
exponent equals `1`, matching the value `1/d` at `d = 1`.
-/

end DDAG


