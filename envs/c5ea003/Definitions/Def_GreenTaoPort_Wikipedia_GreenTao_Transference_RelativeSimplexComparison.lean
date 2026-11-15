-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexComparison
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexComparison
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:04:43.293198+00:00
-- url     : https://prove2.me/theorems/38eef06f-f12c-4e46-864d-516d778f909b
-- title:
--   Face-cut discrepancies between simplex edge functions
-- statement:
--   For real functions $f,g$ on an $r$-coordinate face over a finite type $G$, their correlation against a lower-face cut-test family $u$ is
--
--   $$
--   \mathbb E_x\,(f(x)-g(x))\,\operatorname{CutTestProduct}(u,x).
--   $$
--
--   Face-cut discrepancy at most $\varepsilon$ means that the absolute value of this correlation is at most $\varepsilon$ for every bounded cut test. The edgewise version requires this comparison for each pair of corresponding canonical edge functions of two simplex systems. No positivity of the functions is part of these discrepancy predicates.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeSimplexComparison.lean#L29-L133

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_GeneralRelativeSimplexStep
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Cut-discrepancy comparison of bounded relative simplex states

For an arbitrary simplex edge, the natural discrepancy is tested directly
on its deleted-face coordinates against products of functions omitting one
face coordinate.  This is the same cut-test family used by
`FaceRegularityState.IsFaceCutRegular`, but here it compares two arbitrary
edge functions rather than a function and its conditional expectation.

The existing `simplexMixedCutTest` reconstructs the product of all
non-distinguished factors in an edge-by-edge telescoping term.  Consequently
face-cut discrepancy controls each mixed correlation whenever both simplex
systems are fully bounded.  Summing the correlations gives an actual
weighted-simplex comparison theorem with loss one `ε` per colour.

The final section specializes this comparison to the arbitrary whole-face
functions produced by recursive projection and re-embedding.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Direct face-cut discrepancy -/

/-- Correlation of a difference of arbitrary deleted-face functions with a
product of lower-face tests. -/
noncomputable def faceCutDifferenceCorrelation
    {G : Type*} [Fintype G] {r : ℕ}
    (f g : (Fin r → G) → ℝ)
    (u : CutTestFamily G r) : ℝ :=
  mean fun x =>
    (f x - g x) * cutTestProduct u x

/-- Two arbitrary functions on an `r`-coordinate face are `ε`-close in
face-cut discrepancy. -/
def FaceCutDiscrepancyLe
    {G : Type*} [Fintype G] {r : ℕ}
    (f g : (Fin r → G) → ℝ)
    (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    IsBoundedCutTest u →
      |faceCutDifferenceCorrelation f g u| ≤ ε













/-! ## Edgewise discrepancy for arbitrary weighted simplices -/

/-- Every corresponding pair of canonical simplex edge functions is close
in face-cut discrepancy. -/
def EdgeFaceCutDiscrepancyLe
    {G : Type*} [Fintype G] {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (ε : ℝ) : Prop :=
  ∀ j,
    FaceCutDiscrepancyLe
      (canonicalEdgeFunction H j)
      (canonicalEdgeFunction K j) ε











/-! ## Bridge from the existing AP cut discrepancy -/









/-! ## Projected endpoint comparisons -/















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.faceCutDifferenceCorrelation.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


