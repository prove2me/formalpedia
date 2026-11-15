-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalParameters
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalParameters
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:13:31.033901+00:00
-- url     : https://prove2.me/theorems/49de4a3f-0136-4c94-9a11-4eaaf8b8b553
-- title:
--   Density, defect, and growth schedules for source-full bundle removal
-- statement:
--   At a natural complexity scale $m$, the density threshold is $\delta/(m+1)$. The square-root defect scale is $\eta$ times the $N$th power of that density. A finite rank hierarchy is extended to all natural ranks by clamping at its deepest rank; evaluating the thresholds there gives the density and squared-defect schedules.
--
--   The polynomial growth function is $F(m)=Q(m+1)^N+(m+1)$, which is monotone and lies strictly above the diagonal for natural $Q,N$. The growth-condition certificate records the two scalar inequalities paying for normalized frozen uniformity and energy-gap cleaning:
--
--   $$
--   1\le Q\eta^2\delta^N,
--   \qquad
--   1\le\delta Q^2\eta^2\delta^{2N}.
--   $$
--
--   A bounded realization certificate also retains the numerical ceiling of the ambient-independent plan, bounding its selected rank-zero scale. Positivity conditions used in the later parameter-selection theorem are separate from these total formulas.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullBundleRemovalParameters.lean#L40-L542

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_RankwiseBundleEnvelopeSelection
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
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
# Ambient-independent source-full bundle-removal parameters

This file packages two pieces of the final numerical diagonal.

* `sourceBundleDensity δ m = δ / (m + 1)` pays for a coarse upper
  partition of complexity at most `m` without choosing a global complexity
  window.
* `sourceBundleDefectScale δ η N m = η * sourceBundleDensity δ m ^ N`
  is small relative to every density power up to the fixed finite bundle
  horizon `N`.

The polynomial growth function

```
F(m) = Q * (m + 1)^N + (m + 1)
```

then makes both the common preliminary-regularity tolerance and the
rankwise source energy gaps small at the *same selected scale*.  This is the
pointwise choice which removes the apparent global complexity fixed point.

The last section retains the uniform ceiling supplied by
`SourceFullCoarseTargetSchedule.Bounded` when realizing the numerical plan
over an ambient finite type.  The older `certificate_nonempty` theorem
forgets the landing and hence cannot expose this ceiling to the uniform
count threshold.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Scale-dependent density and defect parameters -/

/-- Density threshold attached to a coarse complexity scale. -/
noncomputable def sourceBundleDensity (δ : ℝ) (m : ℕ) : ℝ :=
  δ / (m + 1 : ℕ)

/-- Square-root defect threshold attached to the same scale. -/
noncomputable def sourceBundleDefectScale
    (δ η : ℝ) (N m : ℕ) : ℝ :=
  η * sourceBundleDensity δ m ^ N















/-! ## Rankwise schedules attached to a selected scale hierarchy -/

/-- Extend a finite selected scale hierarchy to all natural ranks by
clamping at its deepest rank.  Bundle-counting envelopes are indexed by
all naturals even though source-full configurations only query ranks at
most `r`. -/
def sourceBundleSelectedScale
    {r : ℕ} (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℕ :=
  scale ⟨min d r, Nat.lt_succ_iff.mpr (Nat.min_le_right d r)⟩





/-- The density schedule obtained by evaluating `sourceBundleDensity` at
the selected scale of each rank. -/
noncomputable def sourceBundleRankwiseDensity
    {r : ℕ} (δ : ℝ) (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  sourceBundleDensity δ (sourceBundleSelectedScale scale d)

/-- The squared localized-defect schedule paired with the selected
rankwise density schedule. -/
noncomputable def sourceBundleRankwiseDefect
    {r : ℕ} (δ κ : ℝ) (N : ℕ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  sourceBundleDefectScale δ κ N
      (sourceBundleSelectedScale scale d) ^ 2











/-! ## Polynomial pointwise growth -/

/-- A monotone growth function which dominates `Q * (m + 1)^N` at every
scale. -/
def sourceBundleRemovalGrowth (Q N : ℕ) : NatGrowthFunction where
  toFun m := Q * (m + 1) ^ N + (m + 1)
  monotone' := by
    intro a b hab
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_left Q
        (Nat.pow_le_pow_left (Nat.add_le_add_right hab 1) N)
    · exact Nat.add_le_add_right hab 1
  above_diagonal := by
    intro m
    exact (Nat.le_add_left (m + 1) (Q * (m + 1) ^ N))





/-- The two scalar inequalities required of the polynomial coefficient.
The first pays for the normalized frozen-uniformity term and the second for
the source energy-gap cleaning term. -/
structure SourceBundleRemovalGrowthConditions
    (δ η : ℝ) (N Q : ℕ) : Prop where
  uniform :
    1 ≤ (Q : ℝ) * η ^ 2 * δ ^ N
  gap :
    1 ≤ δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N)







/-! ## Finite-horizon normalized counting bounds -/







namespace SourceFullCoarseTargetSchedule.Certificate



end SourceFullCoarseTargetSchedule.Certificate

/-! ## A bounded realized certificate -/

namespace SourceFullCoarseTargetSchedule.Bounded

/-- A realized source-full certificate which remembers the numerical
ceiling of the ambient-independent bounded plan. -/
structure Certificate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F scaleFloor)
    (initial : OrderedPartitionComplex G k r) where
  toSourceFull :
    SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor
  scale_zero_le_ceiling : toSourceFull.scale 0 ≤ S.ceiling



end SourceFullCoarseTargetSchedule.Bounded

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded.Certificate.ctorIdx,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded.Certificate.mk.inj,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded.Certificate.mk.injEq,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded.Certificate.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.SourceFullCoarseTargetSchedule.Bounded.Certificate.noConfusionType,
    `Wikipedia.SzemeredisTheorem.sourceBundleRankwiseDefect.eq_1,
    `Wikipedia.SzemeredisTheorem.sourceBundleRankwiseDensity.eq_1,
    `Wikipedia.SzemeredisTheorem.sourceBundleSelectedScale.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


