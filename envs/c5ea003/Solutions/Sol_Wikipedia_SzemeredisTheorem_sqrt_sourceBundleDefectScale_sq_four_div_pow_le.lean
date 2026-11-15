-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.sqrt_sourceBundleDefectScale_sq_four_div_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:44:39.241718+00:00
-- url     : https://prove2.me/submissions/c002567a-c603-4726-9d42-dd8f73df3a5f

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_AdaptiveCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_GrowthFunctionRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_RankwiseBundleEnvelopeSelection
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_StrongOrderedComplexRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_TowerDominatingGrowth
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
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

section




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





theorem sourceBundleDensity_pos
    {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    0 < sourceBundleDensity δ m := by
  unfold sourceBundleDensity
  positivity

theorem sourceBundleDensity_nonneg
    {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    0 ≤ sourceBundleDensity δ m := by
  unfold sourceBundleDensity
  positivity

theorem sourceBundleDensity_le_one
    {δ : ℝ} (hδ : δ ≤ 1) (hδ0 : 0 ≤ δ) (m : ℕ) :
    sourceBundleDensity δ m ≤ 1 := by
  unfold sourceBundleDensity
  have hden : (1 : ℝ) ≤ (m + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  exact (div_le_self hδ0 hden).trans hδ







theorem sourceBundleDefectScale_nonneg
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (N m : ℕ) :
    0 ≤ sourceBundleDefectScale δ η N m := by
  unfold sourceBundleDefectScale
  exact mul_nonneg hη
    (pow_nonneg (sourceBundleDensity_nonneg hδ m) N)

/-! ## Rankwise schedules attached to a selected scale hierarchy -/





















/-! ## Polynomial pointwise growth -/















/-! ## Finite-horizon normalized counting bounds -/







namespace SourceFullCoarseTargetSchedule.Certificate



end SourceFullCoarseTargetSchedule.Certificate

/-! ## A bounded realized certificate -/

namespace SourceFullCoarseTargetSchedule.Bounded





end SourceFullCoarseTargetSchedule.Bounded

end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Scale-dependent density and defect parameters -/
/-! ## Rankwise schedules attached to a selected scale hierarchy -/
/-! ## Polynomial pointwise growth -/
/-! ## Finite-horizon normalized counting bounds -/

open Wikipedia.SzemeredisTheorem in
/-- The density-scaled defect is small after normalization by every density
power up to its chosen horizon.  The factor four is the lower-error cap
appearing in the reverse-doubling bundle envelope. -/
theorem solution
    {δ κ step : ℝ} {N p m : ℕ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hκ : 0 ≤ κ) (hκ_step : 4 * κ ≤ step)
    (hp : p ≤ N) :
    Real.sqrt
          (sourceBundleDefectScale δ κ N m ^ 2 *
            (1 + (1 : ℝ)) * (1 + (1 : ℝ))) /
        sourceBundleDensity δ m ^ p ≤
      step / 2 := by
  let a := sourceBundleDensity δ m
  let t := sourceBundleDefectScale δ κ N m
  have ha : 0 < a := sourceBundleDensity_pos hδ m
  have ha_one : a ≤ 1 :=
    sourceBundleDensity_le_one hδ_one hδ.le m
  have ht : 0 ≤ t :=
    sourceBundleDefectScale_nonneg hδ.le hκ N m
  have hpow : a ^ N ≤ a ^ p :=
    pow_le_pow_of_le_one ha.le ha_one hp
  have hsqrt :
      Real.sqrt (t ^ 2 * (1 + (1 : ℝ)) * (1 + (1 : ℝ))) =
        2 * t := by
    rw [show
      t ^ 2 * (1 + (1 : ℝ)) * (1 + (1 : ℝ)) =
        (2 * t) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (by norm_num) ht)
  rw [show sourceBundleDefectScale δ κ N m = t by rfl,
    show sourceBundleDensity δ m = a by rfl, hsqrt]
  have hnormalized : 2 * t / a ^ p ≤ 2 * κ := by
    apply (div_le_iff₀ (pow_pos ha p)).2
    calc
      2 * t = (2 * κ) * a ^ N := by
        dsimp [t, a, sourceBundleDefectScale]
        ring
      _ ≤ (2 * κ) * a ^ p :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
  exact hnormalized.trans (by linarith)
