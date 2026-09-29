-- Prove2me | Theorems.Thm_CategoricalTropicalUltrametric_d_cons_same
-- name    : CategoricalTropicalUltrametric.d_cons_same
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:38:38.081418+00:00
-- url     : https://prove2.me/theorems/6be66a9d-84b6-4681-9a65-a225c2f7bdee
-- title:
--   Half-scale similarity.
-- statement:
--   **Half-scale similarity.**  Inserting the same branch label halves all distances:
--   the Berggren boundary is self-similar with contraction factor exactly `1/2`.
--
--   ```lean
--   theorem CategoricalTropicalUltrametric.d_cons_same(k : Fin 3) (x y : Addr) :
--       d (cons k x) (cons k y) = (1 / 2 : ℝ) * d x y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/BerggrenTrees/BerggrenBoundaryUltrametric.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/BerggrenTrees/BerggrenBoundaryUltrametric.lean#L158

-- Thm stub generated from Bridges/BerggrenTrees/BerggrenBoundaryUltrametric.lean
import Mathlib
import Definitions.Def_Bridges_BerggrenTrees_BerggrenBoundaryUltrametric
/-
  # The Berggren Boundary Ultrametric (Conjecture C1, analytic half)

  The ternary Berggren tree of primitive Pythagorean triples is a rooted `3`-ary tree:
  every primitive triple has exactly three children `A`, `B`, `C`.  An infinite descent
  through the tree is therefore an *address* `x : ℕ → Fin 3`, and the set of all such
  addresses is the boundary `Addr` of the tree.

  This file supplies the bespoke tree ultrametric

  `d x y = 2 ^ (-firstDiff x y)`,  `firstDiff x y = min { n | x n ≠ y n }`,

  together with all the axioms needed to package it as a Mathlib `MetricSpace` and
  `IsUltrametricDist` (which is done in `FunctorialTropicalPythagoreanMetric.lean`):
  `d_self`, `d_comm`, `d_nonneg`, `d_eq_zero_iff`, `d_ultra`, `d_triangle`, `d_le_one`,
  and the two branch lemmas `d_cons_same` (each branch insertion is an exact `1/2`
  similarity) and `d_cons_diff` (distinct branches are maximally separated).

  -- !-- Lab Notes -- !--
  HYPOTHESIS: the "first place where two descents through the Berggren tree diverge"
  is a genuine ultrametric, and branch insertion `cons k` scales it by exactly `1/2`.
  EXPERIMENT: define `firstDiff` as `sInf {n | x n ≠ y n}` and characterise it by the
  pair (`differs at n`, `agrees below n`); everything else follows from that lemma.
  ANALYSIS: the strong triangle inequality needs no induction — at the first index
  where `x` and `z` differ, one of `x, y` or `y, z` must already differ, so one of the
  two distances is at least `d x z`.
  CRITIQUE: `firstDiff x x = 0` by the `sInf ∅ = 0` convention, so `d` must be defined
  by a case split on `x = y`; every lemma below is stated for the case-split version.
-/

open CategoricalTropicalUltrametric

open Classical

theorem CategoricalTropicalUltrametric.d_cons_same(k : Fin 3) (x y : Addr) :
    d (cons k x) (cons k y) = (1 / 2 : ℝ) * d x y := by sorry
