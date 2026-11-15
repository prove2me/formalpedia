-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.sourceFullRankGap_div_sourceBundleDefectScale_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:44:39.214141+00:00
-- url     : https://prove2.me/submissions/df3a84ae-556f-4934-9e34-f8beec965b90

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
# One-rank growth-function regularity

This file packages the preliminary one-rank selector underlying the
growth-function form of hypergraph regularity.  For a natural-valued growth
function `F`, an initial complexity bound `M₀`, and a fixed upper layer, the
schedule is constructed triangularly:

```
M 0       = M₀,
τ n       = 1 / F (M n),
B n       = ⌈card (OrderedFace k (j + 1)) / (τ n)²⌉ + 1,
M (n + 1) = (2^(j+1))^(B n) * M n.
```

The existing fixed-upper tower then selects adjacent coarse and fine stages.
The fine stage is preliminarily regular with error exactly `τ i`; a
one-rank energy pigeonhole makes the coarse/fine gap at most any prescribed
positive `γ`.  All numerical schedules are ambient-independent.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Natural growth functions -/



namespace NatGrowthFunction





theorem positive (F : NatGrowthFunction) (n : ℕ) :
    0 < F n := by
  exact lt_of_lt_of_le (Nat.zero_lt_succ n)
    (F.above_diagonal n)



end NatGrowthFunction

/-! ## The triangular numerical schedule -/

































/-! ## A one-rank energy timescale -/







/-! ## Growth-function fixed-upper selection -/





end Wikipedia.SzemeredisTheorem

end

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









theorem sourceBundleDefectScale_pos
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (N m : ℕ) :
    0 < sourceBundleDefectScale δ η N m := by
  unfold sourceBundleDefectScale
  exact mul_pos hη (pow_pos (sourceBundleDensity_pos hδ m) N)



/-! ## Rankwise schedules attached to a selected scale hierarchy -/





















/-! ## Polynomial pointwise growth -/



@[simp]
theorem sourceBundleRemovalGrowth_apply
    (Q N m : ℕ) :
    sourceBundleRemovalGrowth Q N m =
      Q * (m + 1) ^ N + (m + 1) :=
  rfl

theorem sourceBundleRemovalGrowth_polynomial_le
    (Q N m : ℕ) :
    Q * (m + 1) ^ N ≤ sourceBundleRemovalGrowth Q N m := by
  rw [sourceBundleRemovalGrowth_apply]
  exact Nat.le_add_right _ _









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

open Wikipedia.SzemeredisTheorem in
/-- After division by the scale-dependent squared defect threshold, the
source rank-gap target costs at most `δ`. -/
theorem solution
    {δ η : ℝ} {N Q : ℕ}
    (hδ : 0 < δ) (hη : 0 < η)
    (hQ : SourceBundleRemovalGrowthConditions δ η N Q)
    (m : ℕ) :
    (1 / (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2) /
          sourceBundleDefectScale δ η N m ^ 2 ≤
      δ := by
  have hx : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hF : (0 : ℝ) < sourceBundleRemovalGrowth Q N m := by
    exact_mod_cast (sourceBundleRemovalGrowth Q N).positive m
  have ht : 0 < sourceBundleDefectScale δ η N m :=
    sourceBundleDefectScale_pos hδ hη N m
  rw [div_le_iff₀ (sq_pos_of_pos ht)]
  rw [div_le_iff₀ (sq_pos_of_pos hF)]
  have hpoly :
      (Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N ≤
        (sourceBundleRemovalGrowth Q N m : ℕ) := by
    exact_mod_cast sourceBundleRemovalGrowth_polynomial_le Q N m
  have hpolySq :
      ((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) ^ 2 ≤
        (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 := by
    exact
      (sq_le_sq₀
        (mul_nonneg (Nat.cast_nonneg Q) (pow_nonneg hx.le N))
        hF.le).2 hpoly
  calc
    1 ≤ δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N) := hQ.gap
    _ =
        δ * (((Q : ℝ) * ((m + 1 : ℕ) : ℝ) ^ N) ^ 2 *
          sourceBundleDefectScale δ η N m ^ 2) := by
      unfold sourceBundleDefectScale sourceBundleDensity
      rw [div_pow]
      field_simp
      ring
    _ ≤
        δ * ((sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 *
          sourceBundleDefectScale δ η N m ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      exact mul_le_mul_of_nonneg_right hpolySq (sq_nonneg _)
    _ =
        δ * sourceBundleDefectScale δ η N m ^ 2 *
          (sourceBundleRemovalGrowth Q N m : ℝ) ^ 2 := by
      ring
