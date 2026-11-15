-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.sourceBundleRankwiseEnvelope_and_error_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:45:55.826219+00:00
-- url     : https://prove2.me/submissions/5b4279c5-3bbb-4f14-bb13-a1bde812d6b4

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
import Theorems.Thm_Wikipedia_SzemeredisTheorem_one_div_sourceBundleRemovalGrowth_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sqrt_sourceBundleDefectScale_sq_four_div_pow_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Rankwise numerical envelopes for bundle counting

The generalized bundle-counting recurrence permits the density and
localized-defect parameters to depend on the rank.  This file supplies a
direct numerical envelope for those rankwise parameters.  Its density floor
is the prefix minimum of the rankwise densities, so no global density lower
bound is needed.

The row constructor takes a maximum with the preceding-order row.  This
makes monotonicity in bundle order automatic even when consecutive ranks use
unrelated parameters; its other branch is equality in the one-edge counting
recurrence.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-! ## Prefix density floors -/





@[simp]
theorem bundleRankwiseDensityFloor_succ (α : ℕ → ℝ) (d : ℕ) :
    bundleRankwiseDensityFloor α (d + 1) =
      min (bundleRankwiseDensityFloor α d) (α (d + 1)) :=
  rfl







/-! ## The rankwise recurrence -/







@[simp]
theorem bundleRankwiseNextRow_zero
    (α β μ : ℕ → ℝ) (τ : ℝ) (d : ℕ) (lower : ℕ → ℝ) :
    bundleRankwiseNextRow α β μ τ d lower 0 = 0 :=
  rfl



@[simp]
theorem bundleRankwiseEnvelopeError_zero_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ 0 n = 0 :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_succ_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ (d + 1) n =
      bundleRankwiseNextRow α β μ τ d
        (bundleRankwiseEnvelopeError α β μ τ d) n :=
  rfl

/-! ## Positivity and monotonicity -/















/-! ## The generalized-counting interface -/



/-! ## Vanishing and continuous rankwise parameter paths -/









/-! ## Density-scaled finite-horizon selection -/



















/-! ## Explicit finite-horizon sufficient bounds -/





theorem bundleReverseDoublingHorizon_le_zero
    (rankBound edgeBound d : ℕ) :
    bundleReverseDoublingHorizon rankBound edgeBound d ≤
      bundleReverseDoublingHorizon rankBound edgeBound 0 := by
  unfold bundleReverseDoublingHorizon
  apply Nat.mul_le_mul_left
  exact (pow_right_monotone (by norm_num : (1 : ℕ) ≤ 2))
    (Nat.sub_le rankBound d)









end Wikipedia.SzemeredisTheorem

end

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
# Source-style full coarse-target regularity

Tao's full regularity lemma does not choose the parameters at the different
ranks independently.  It first fixes a lower scale and then descends through
the ranks with a sufficiently fast auxiliary growth function.  The selected
scales have the shape

```
scaleFloor ≤ M_r,
F(M_{j + 1}) ≤ M_j,
gap_j ≤ 1 / F(M_{j + 1})^2,
regularity_j ≤ 1 / F(M_0).
```

This file isolates the exact adaptive certificate needed for that induction.
A `SourceFullCoarseTargetSchedule` is a finite top-down decision tree together
with numerical scale data on its genuine landings.  Its hypotheses are all
finite and ambient-independent.  The main compiler realizes the tree by
`AdaptiveCoarseTargetSchedule.exists_landing_certificate` and returns an
ordinary `CoarseTargetOrderedComplexRegularityCertificate` carrying the
source-style scale hierarchy.

The rank-zero plan and a genuine successor constructor are proved below.
The successor constructor makes the remaining mathematical obligation
explicit: after the current top index is selected, the lower plan must have
been built with scale floor `F(topScale)`, and the already fixed top
tolerance must be bounded by the common reciprocal attached to every landing
of that lower plan.  Constructing these lower plans uniformly is precisely
the auxiliary faster-growth induction in the source proof.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Source numerical targets -/





theorem sourceFullCommonTolerance_pos
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ) :
    0 < sourceFullCommonTolerance F scale := by
  unfold sourceFullCommonTolerance
  exact one_div_pos.mpr
    (by exact_mod_cast F.positive (scale 0))



/-! ## Numerical bounds selected by an adaptive landing -/



/-! ## Adaptive source-full plans -/



namespace SourceFullCoarseTargetSchedule





/-! ## Realized source-full certificates -/





/-! ## Rank-zero plan -/





/-! ## A genuine top-down successor constructor -/















/-! ## The finite faster-growth induction -/



namespace Bounded



end Bounded



































end SourceFullCoarseTargetSchedule

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



theorem sourceBundleDensity_le_one
    {δ : ℝ} (hδ : δ ≤ 1) (hδ0 : 0 ≤ δ) (m : ℕ) :
    sourceBundleDensity δ m ≤ 1 := by
  unfold sourceBundleDensity
  have hden : (1 : ℝ) ≤ (m + 1 : ℕ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  exact (div_le_self hδ0 hden).trans hδ

theorem sourceBundleDensity_antitone
    {δ : ℝ} (hδ : 0 ≤ δ) :
    Antitone (sourceBundleDensity δ) := by
  intro a b hab
  unfold sourceBundleDensity
  apply div_le_div_of_nonneg_left hδ
  · positivity
  · exact_mod_cast Nat.add_le_add_right hab 1







/-! ## Rankwise schedules attached to a selected scale hierarchy -/



@[simp]
theorem sourceBundleSelectedScale_zero
    {r : ℕ} (scale : Fin (r + 1) → ℕ) :
    sourceBundleSelectedScale scale 0 = scale 0 := by
  simp [sourceBundleSelectedScale]







theorem sourceBundleRankwiseDensity_pos
    {r : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    0 < sourceBundleRankwiseDensity δ scale d :=
  sourceBundleDensity_pos hδ _

theorem sourceBundleRankwiseDensity_le_one
    {r : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (hδ_one : δ ≤ 1)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    sourceBundleRankwiseDensity δ scale d ≤ 1 :=
  sourceBundleDensity_le_one hδ_one hδ _

theorem sourceBundleRankwiseDefect_nonneg
    {r : ℕ} (δ κ : ℝ) (N : ℕ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) :
    0 ≤ sourceBundleRankwiseDefect δ κ N scale d :=
  sq_nonneg _

/-- Antitonicity of the selected scales makes rank zero the least density
in the extended rankwise density schedule. -/
theorem sourceBundleRankwiseDensity_zero_le
    {r : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    {scale : Fin (r + 1) → ℕ} (hscale : Antitone scale)
    (d : ℕ) :
    sourceBundleRankwiseDensity δ scale 0 ≤
      sourceBundleRankwiseDensity δ scale d := by
  apply sourceBundleDensity_antitone hδ
  exact hscale (Fin.zero_le _)

/-- If the zeroth entry is a lower bound for a schedule, it is also a
lower bound for every finite prefix minimum. -/
theorem le_bundleRankwiseDensityFloor_of_zero_le
    {α : ℕ → ℝ} (hα : ∀ d, α 0 ≤ α d) :
    ∀ d, α 0 ≤ bundleRankwiseDensityFloor α d := by
  intro d
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
      rw [bundleRankwiseDensityFloor_succ]
      exact le_min ih (hα (d + 1))

/-! ## Polynomial pointwise growth -/















/-! ## Finite-horizon normalized counting bounds -/



/-- A tolerance bounded by `κ² a^N` remains at most `κ²` after
normalization by any larger density floor to a power at most `N`. -/
theorem div_pow_le_sq_of_le_scaled_pow
    {τ κ a μ : ℝ} {p N : ℕ}
    (ha : 0 < a) (ha_one : a ≤ 1) (haμ : a ≤ μ)
    (hτ : τ ≤ κ ^ 2 * a ^ N) (hp : p ≤ N) :
    τ / μ ^ p ≤ κ ^ 2 := by
  have hμ : 0 < μ := ha.trans_le haμ
  have hpow₁ : a ^ N ≤ a ^ p :=
    pow_le_pow_of_le_one ha.le ha_one hp
  have hpow₂ : a ^ p ≤ μ ^ p :=
    pow_le_pow_left₀ ha.le haμ p
  apply (div_le_iff₀ (pow_pos hμ p)).2
  exact hτ.trans
    (mul_le_mul_of_nonneg_left (hpow₁.trans hpow₂) (sq_nonneg κ))



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
/-- The explicit source-full hierarchy, viewed just as a selected scale
array, feeds the reverse-doubling bundle envelope.  All hypotheses are
scalar and ambient-independent. -/
theorem solution
    {r edgeBound Q : ℕ} {δ κ step : ℝ}
    (hδ : 0 < δ) (hδ_one : δ ≤ 1)
    (hκ : 0 < κ) (hstep : 0 ≤ step)
    (hκ_step : 4 * κ ≤ step)
    (hκ_sq : κ ^ 2 ≤ step / 2)
    (hcap :
      (r : ℝ) *
          (bundleReverseDoublingHorizon r edgeBound 0 : ℝ) * step ≤ 1)
    (hfinal :
      (r : ℝ) *
          (bundleReverseDoublingHorizon r edgeBound 0 : ℝ) * step < 1 / 2)
    (hQ : SourceBundleRemovalGrowthConditions δ κ
      (bundleReverseDoublingHorizon r edgeBound 0) Q)
    (scale : Fin (r + 1) → ℕ) (hscale : Antitone scale) :
    IsBundleCountingEnvelope
        (sourceBundleRankwiseDensity δ scale)
        (sourceBundleRankwiseDefect δ κ
          (bundleReverseDoublingHorizon r edgeBound 0) scale)
        (bundleRankwiseDensityFloor
          (sourceBundleRankwiseDensity δ scale))
        (sourceFullCommonTolerance
          (sourceBundleRemovalGrowth Q
            (bundleReverseDoublingHorizon r edgeBound 0)) scale)
        (bundleRankwiseEnvelopeError
          (sourceBundleRankwiseDensity δ scale)
          (sourceBundleRankwiseDefect δ κ
            (bundleReverseDoublingHorizon r edgeBound 0) scale)
          (bundleRankwiseDensityFloor
            (sourceBundleRankwiseDensity δ scale))
          (sourceFullCommonTolerance
            (sourceBundleRemovalGrowth Q
              (bundleReverseDoublingHorizon r edgeBound 0)) scale)) ∧
      bundleRankwiseEnvelopeError
          (sourceBundleRankwiseDensity δ scale)
          (sourceBundleRankwiseDefect δ κ
            (bundleReverseDoublingHorizon r edgeBound 0) scale)
          (bundleRankwiseDensityFloor
            (sourceBundleRankwiseDensity δ scale))
          (sourceFullCommonTolerance
            (sourceBundleRemovalGrowth Q
              (bundleReverseDoublingHorizon r edgeBound 0)) scale)
          r edgeBound < 1 / 2 := by
  let N := bundleReverseDoublingHorizon r edgeBound 0
  let α := sourceBundleRankwiseDensity δ scale
  let β := sourceBundleRankwiseDefect δ κ N scale
  let μ := bundleRankwiseDensityFloor α
  let τ := sourceFullCommonTolerance
    (sourceBundleRemovalGrowth Q N) scale
  have hα : ∀ d, 0 < α d := by
    intro d
    exact sourceBundleRankwiseDensity_pos hδ scale d
  have hα_one : ∀ d, α d ≤ 1 := by
    intro d
    exact sourceBundleRankwiseDensity_le_one hδ.le hδ_one scale d
  have hβ : ∀ d, 0 ≤ β d := by
    intro d
    exact sourceBundleRankwiseDefect_nonneg δ κ N scale d
  have hτ : 0 ≤ τ := by
    exact (sourceFullCommonTolerance_pos
      (sourceBundleRemovalGrowth Q N) scale).le
  have hαzero : ∀ d, α 0 ≤ α d := by
    intro d
    exact sourceBundleRankwiseDensity_zero_le hδ.le hscale d
  have hfinitePower :
      ∀ d, d < r → ∀ n,
        n < bundleReverseDoublingHorizon r edgeBound (d + 1) →
          n + 1 ≤ N := by
    intro d _hd n hn
    have hhorizon :=
      bundleReverseDoublingHorizon_le_zero r edgeBound (d + 1)
    dsimp only [N]
    omega
  apply
    (bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
      hα hα_one hβ hτ hstep r edgeBound hcap hfinal)
  · intro d hd n hn
    have hp := hfinitePower d hd n hn
    simpa only [α, β, N, sourceBundleRankwiseDefect,
      sourceBundleRankwiseDensity] using
      (sqrt_sourceBundleDefectScale_sq_four_div_pow_le
        hδ hδ_one hκ.le hκ_step hp)
  · intro d hd n hn
    have hp := hfinitePower d hd n hn
    have ha0 : 0 < α 0 := hα 0
    have ha0_one : α 0 ≤ 1 := hα_one 0
    have ha0μ : α 0 ≤ μ (d + 1) :=
      le_bundleRankwiseDensityFloor_of_zero_le hαzero (d + 1)
    have hτscaled : τ ≤ κ ^ 2 * (α 0) ^ N := by
      simpa only [τ, α, N, sourceFullCommonTolerance,
        sourceBundleRankwiseDensity, sourceBundleSelectedScale_zero] using
        (one_div_sourceBundleRemovalGrowth_le hδ hκ hQ (scale 0))
    exact
      (div_pow_le_sq_of_le_scaled_pow
        ha0 ha0_one ha0μ hτscaled hp).trans hκ_sq
