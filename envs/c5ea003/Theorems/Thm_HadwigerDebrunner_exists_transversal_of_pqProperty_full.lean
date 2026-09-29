-- Prove2me | Theorems.Thm_HadwigerDebrunner_exists_transversal_of_pqProperty_full
-- name    : HadwigerDebrunner.exists_transversal_of_pqProperty_full
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:22:38.755462+00:00
-- url     : https://prove2.me/theorems/082aad24-af7b-462b-b90d-58edced7eff6
-- title:
--   Elementary transversal bound.
-- statement:
--   **Elementary transversal bound.**  If `F` has the *full* `(|s|, q)`-property
--   (among the whole family, some `q` members share a point) and every member is
--   nonempty, then `F` has a transversal of size at most `|s| - q + 1`.
--
--   The shared point of the `q` members pierces all of them at once; the remaining
--   `|s| - q` members are pierced one point each.
--
--   (The hypothesis `q ≤ |s|` is not needed thanks to truncated natural subtraction,
--   so it is omitted.)
--
--   ```lean
--   theorem HadwigerDebrunner.exists_transversal_of_pqProperty_full{s : Finset ι} {F : ι → Set X} {q : ℕ}
--       (hne : ∀ i ∈ s, (F i).Nonempty)
--       (hpq : HasPQProperty s F s.card q) :
--       ∃ T : Finset X, IsTransversal T s F ∧ T.card ≤ s.card - q + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/HadwigerDebrunner/Combinatorial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/HadwigerDebrunner/Combinatorial.lean#L80

-- Thm stub generated from Geometry/HadwigerDebrunner/Combinatorial.lean
import Mathlib
import Definitions.Def_Geometry_HadwigerDebrunner_Combinatorial
/-
# Hadwiger–Debrunner `(p,q)`-property: the combinatorial core

This file develops the *set-class agnostic* combinatorial skeleton underlying the
Hadwiger–Debrunner `(p,q)` transversal theory.  Nothing here depends on convexity
or on a dimension: we work with an arbitrary finite family `F : ι → Set X`
indexed by a `Finset s`, and isolate exactly the combinatorial content of the
`(p,q)`-property and of *transversals* (piercing sets).

The two genuinely combinatorial facts proved here are:

* monotonicity of the `(p,q)`-property (strengthen `p`, weaken `q`); and
* the elementary transversal bound coming from the *full* `(|s|, q)`-property:
  if some `q` members share a point, that single point pierces all `q` of them,
  so the whole family is pierced by `|s| - q + 1` points.

These are the ingredients that are *independent of the Helly number*; the
Helly-number input (which is where dimension and the convex-vs-splinter
distinction enters, `d+1` vs `2d+1`) is supplied in `HellyBridge.lean`.

## Main results

* `HasPQProperty.strengthen_p` : the `(p,q)`-property implies the `(p',q)`-property for `p ≤ p'`.
* `HasPQProperty.weaken_q`     : the `(p,q)`-property implies the `(p,q')`-property for `q' ≤ q`.
* `exists_transversal_of_nonempty` : every family of nonempty sets has a transversal of size `≤ |s|`.
* `exists_transversal_of_pqProperty_full` : the `(|s|, q)`-property yields a transversal of size `≤ |s| - q + 1`.
-/


open Finset

open HadwigerDebrunner

variable {ι X : Type*}



/-
Strengthening `p`: the `(p,q)`-property implies the `(p',q)`-property whenever
`p ≤ p'`.  (Among every `p'` members, look at any `p` of them.)
-/

/-
Weakening `q`: the `(p,q)`-property implies the `(p,q')`-property whenever
`q' ≤ q`.  (A common point of `q` sets is a common point of any `q'` of them.)
-/

/-
A family of nonempty sets always has a transversal of size at most `|s|`:
pick one point from each member.
-/

theorem HadwigerDebrunner.exists_transversal_of_pqProperty_full{s : Finset ι} {F : ι → Set X} {q : ℕ}
    (hne : ∀ i ∈ s, (F i).Nonempty)
    (hpq : HasPQProperty s F s.card q) :
    ∃ T : Finset X, IsTransversal T s F ∧ T.card ≤ s.card - q + 1 := by sorry
