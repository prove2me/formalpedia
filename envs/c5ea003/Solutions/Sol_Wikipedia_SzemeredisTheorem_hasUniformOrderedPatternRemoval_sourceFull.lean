-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.hasUniformOrderedPatternRemoval_sourceFull
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:54:46.856602+00:00
-- url     : https://prove2.me/submissions/0b31cc45-f48e-4f3f-b8d4-541a4c990166

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_AdaptiveCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_GrowthFunctionRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationStep
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFrozenCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFrozenUniformity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleSourceGoodnessBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedFullBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPatternPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalTheorem
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_RankwiseBundleEnvelopeSelection
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalAssembly
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullOrderedRemoval
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_OrderedCoarseFineComplex_faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SourceFullCoarseTargetSchedule_Bounded_certificate_nonempty
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SourceFullCoarseTargetSchedule_bounded_nonempty
import Theorems.Thm_Wikipedia_SzemeredisTheorem_card_mul_two_sourceBundleRemovalDensityBudget_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_complexity_orderedPatternInitialComplex_le_two
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_sourceBundleRemovalGrowthCoefficient
import Theorems.Thm_Wikipedia_SzemeredisTheorem_half_rankwiseDensityProduct_le_fullConfigurationCount
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sourceBundleRankwiseEnvelope_and_error_lt_half
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sourceBundleRemovalStep_total_le_quarter
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sourceFullBadBaseDeletionFamily_isCover_of_sourceFullMixedGood_count
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sourceFullRankGap_div_sourceBundleDefectScale_sq_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl





























































end Wikipedia.SzemeredisTheorem

end

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















end Wikipedia.SzemeredisTheorem

end

section


/-!
# Bernoulli reduction for bounded boundary products

The preliminary shared-face regularity lemma is stated using Boolean
products on the immediate boundary of an upper face.  This file proves that
this loses no generality for products of arbitrary `[0,1]`-valued boundary
factors.

At successor arity the ordinary `CutTestFamily` coordinates are exactly the
boundary coordinates.  The only formal difference is that
`BooleanCutAssignment` uses an uncurried product index whereas
`BoundaryBooleanCutAssignment` is curried.  After recording the equivalence
between those two presentations, the finite Bernoulli-mixture identities
from `BooleanCutReduction` give:

* every bounded boundary factor is a convex average of Boolean component
  indicators;
* every bounded boundary product is a convex average of
  `boundaryBooleanCutSupport` indicators;
* Boolean preliminary regularity therefore controls every bounded boundary
  product with the same error.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





















/-- At successor arity the specialized boundary erasure is the ordinary
cut-test coordinate erasure. -/
theorem eraseBoundaryCoordinate_eq_eraseCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    eraseBoundaryCoordinate i x = eraseCoordinate i x :=
  rfl









namespace FaceRegularityState





end FaceRegularityState





end Wikipedia.SzemeredisTheorem

end

section






/-!
# Passing from fine upper atoms to coarse upper atoms

Strong ordered regularity naturally controls every atom of a fine upper
partition, while the removal argument benefits from choosing its closed
configuration in a fixed coarse complex.  This file supplies the finite
bridge between those two choices.

For a refinement `fineUpper ≤ coarseUpper`, every coarse atom is the
disjoint union of the fine atoms which it contains.  Consequently its
indicator is their sum.  Linearity then transfers cut regularity, with the
number of contained fine atoms as the exact loss.  The same decomposition,
followed by finite Cauchy--Schwarz and a fiberwise sum, controls the
coarse-upper atom-energy gap by the fine-upper gap with only one fine
complexity factor.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Coarse fibers of fine atoms -/



















/-! ## Linear transfer of cut regularity -/

















/-! ## Coarse-upper atom-energy gaps -/













namespace OrderedCoarseFineComplex



/-- Coarse-upper local gaps are nonnegative. -/
theorem coarseUpperFaceAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    0 ≤ P.coarseUpperFaceAtomEnergyGap j e := by
  apply sub_nonneg.mpr
  exact orderedAtomEnergy_mono
    (fun f => P.refines j.castSucc f)
    e (P.coarse.partition j.succ e)





/-- A coarse-upper layer gap is the sum of its local face gaps. -/
theorem coarseUpperLayerAtomEnergyGap_eq_sum_face
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    P.coarseUpperLayerAtomEnergyGap j =
      ∑ e : OrderedFace k (j.1 + 1),
        P.coarseUpperFaceAtomEnergyGap j e := by
  unfold coarseUpperLayerAtomEnergyGap
    coarseUpperFaceAtomEnergyGap
    orderedLayerAtomEnergy
  rw [Finset.sum_sub_distrib]
  rfl







end OrderedCoarseFineComplex

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
# The ordered configuration as an initial hypergraph bundle

The generalized bundle counting lemma starts from the bundle having one
occurrence vertex above each vertex class.  Its edges are the empty edge
and the ranges of all positive ordered faces.  This file identifies that
initial bundle, its indicator weights, and its main-density product with
the ordered-configuration objects used by the removal argument.

The only small bookkeeping issue is that an ordered face is an increasing
map `Fin n ↪o Fin k`, whereas a bundle edge is a `Finset (Fin k)`.  A
nonempty finite set has a unique increasing enumeration, supplied by
`Finset.orderEmbOfFin`; the equivalence below packages this canonical
change of indices.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Positive ordered faces as nonempty finite edges -/























/-! ## The complete initial bundle -/











@[simp]
theorem orderedConfigurationInitialBundle_edges
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).edges =
      orderedConfigurationBaseEdges k r :=
  rfl





/-! ## Canonical local tuples and base weights -/















/-! ## Main densities -/









/-! ## Exact initial count and product identities -/













end Wikipedia.SzemeredisTheorem

end

section


/-!
# Full lower boundaries of ordered faces

The source hypergraph regularity argument conditions an upper face on the
join of the partitions carried by *all* of its nonempty proper subfaces.
The adjacent-rank boundary in `OrderedBoundaryPartition` is enough to encode
closedness, but it does not expose this source-level sigma algebra directly.

This file constructs that full lower boundary.  A proper positive subface of
an `n + 1` tuple is represented by a positive ordered face of that tuple
whose rank is at most `n`.  Each genuine partition in the ambient ordered
complex is pulled back to the selected upper tuple space, and the full lower
boundary is their finite common refinement.

The last section packages the coarse/fine defect and the corresponding
source mixed-goodness condition.  Its principal consequence is the localized
weighted square-defect estimate on the selected full-lower atom.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Proper positive subfaces -/





/-! ## The full lower partition -/







/-- Restricting through the ambient face agrees with first selecting the
upper tuple and then selecting its local proper subface. -/
@[simp]
theorem orderedFaceTuple_orderedFullLowerAmbientFace
    {G : Type*} {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1)
    (x : Fin k → G) :
    orderedFaceTuple (orderedFullLowerAmbientFace e d) x =
      orderedFaceTuple d.face (orderedFaceTuple e.face x) :=
  rfl























/-! ## Selected full-lower atoms and their weights -/





















/-! ## Source full-lower goodness -/























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

/-- The low-density cleaning term at scale `m` costs at most `δ`. -/
theorem mul_sourceBundleDensity_le
    {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    (m : ℝ) * sourceBundleDensity δ m ≤ δ := by
  unfold sourceBundleDensity
  have hden : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  calc
    (m : ℝ) * (δ / (m + 1 : ℕ)) =
        δ * ((m : ℝ) / (m + 1 : ℕ)) := by ring
    _ ≤ δ * 1 := by
      apply mul_le_mul_of_nonneg_left _ hδ
      exact (div_le_one hden).2 (by norm_num)
    _ = δ := mul_one δ

theorem sourceBundleDefectScale_pos
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (N m : ℕ) :
    0 < sourceBundleDefectScale δ η N m := by
  unfold sourceBundleDefectScale
  exact mul_pos hη (pow_pos (sourceBundleDensity_pos hδ m) N)



/-! ## Rankwise schedules attached to a selected scale hierarchy -/





theorem sourceBundleSelectedScale_of_le
    {r d : ℕ} (scale : Fin (r + 1) → ℕ) (hd : d ≤ r) :
    sourceBundleSelectedScale scale d =
      scale ⟨d, Nat.lt_succ_iff.mpr hd⟩ := by
  simp [sourceBundleSelectedScale, Nat.min_eq_left hd]





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





/-! ## Polynomial pointwise growth -/















/-! ## Finite-horizon normalized counting bounds -/







namespace SourceFullCoarseTargetSchedule.Certificate

/-- The scale hierarchy stored in a realized source-full certificate is
antitone. -/
theorem scale_antitone
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (C : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor) :
    Antitone C.scale := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.above_diagonal (C.scale j.succ)).trans
        (C.scale_hierarchy j))

end SourceFullCoarseTargetSchedule.Certificate

/-! ## A bounded realized certificate -/

namespace SourceFullCoarseTargetSchedule.Bounded





end SourceFullCoarseTargetSchedule.Bounded

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Rankwise source-full bundle counting

The source full-regularity hierarchy supplies a different density and
defect threshold at each positive rank, together with one common
fine-boundary regularity error.  This file assembles those data directly
with the generalized bundle-counting envelope.

Unlike `SourceFullBundleCounting`, no parameter is required to be constant
in the rank.  The final lower bound is quantitative: if the chosen envelope
has error below one half, then every source-full good closed configuration
has count at least one half of the product of its prescribed rankwise
density floors.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## The finite horizon of the initial configuration bundle -/

/-- Every edge of the initial ordered-configuration bundle has cardinality
at most the complex rank. -/
theorem orderedConfigurationInitialBundle_order_le
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).order ≤ r := by
  unfold HypergraphBundle.order
  rw [orderedConfigurationInitialBundle_edges]
  apply Finset.sup_le
  intro e he
  exact (mem_orderedConfigurationBaseEdges_iff e).1 he

/-! ## The source-full regularity certificate as a counting input -/

/-- The selected mixed-regularity tolerances in a source-full certificate
are all bounded by its advertised common reciprocal tolerance. -/
theorem SourceFullCoarseTargetSchedule.Certificate.isFullyMixedPreliminaryOrderedRegular_common
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (R : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor) :
    IsFullyMixedPreliminaryOrderedRegular
      R.regularity.toCoarseFine
      (fun _ => sourceFullCommonTolerance F R.scale) := by
  intro j e a b
  exact
    (R.regularity.mixedRegular j e a b).trans
      (R.selected_tolerance_le_common j)

/-! ## Rankwise base-density and one-edge inputs -/





/-! ## Relative counting with an arbitrary rankwise envelope -/



/-! ## Initial configuration and a uniform quantitative lower bound -/





/-- It is enough to control the envelope at the ambient complex rank:
the initial configuration bundle has order at most that rank, and every
valid envelope is monotone in its order argument. -/
theorem half_rankwiseDensityProduct_le_fullConfigurationCount_of_rankBound
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hα : ∀ d, 0 < α d)
    (hαone : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    (herror :
      E r (orderedConfigurationInitialBundle k r).edges.card <
        1 / 2) :
    (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) ≤
      fullConfigurationCount A := by
  apply
    half_rankwiseDensityProduct_le_fullConfigurationCount
      P A α β μ τ E hα hαone hβ hτ hgood hregular henvelope
  exact
    (henvelope.error_mono_order
      (orderedConfigurationInitialBundle_order_le k r)).trans_lt
      herror

end Wikipedia.SzemeredisTheorem

end

section







/-!
# Source-full bundle-counting removal assembly

This file joins the ambient-independent source-full regularity plan to the
rankwise bundle-counting theorem and the source-full bad-base deletion family.
The selected regularity scale is clipped to the finite rank horizon.  Since
the selected scales decrease with rank while `sourceBundleDensity` decreases
with its scale, the resulting density schedule increases with rank; hence its
bundle prefix floor is exactly its rank-zero value.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Ambient-independent scalar budgets -/









theorem sourceBundleRemovalDensityBudget_pos
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    0 < sourceBundleRemovalDensityBudget ε r := by
  unfold sourceBundleRemovalDensityBudget
  positivity

theorem sourceBundleRemovalDensityBudget_le_one
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    sourceBundleRemovalDensityBudget ε r ≤ 1 := by
  unfold sourceBundleRemovalDensityBudget
  have hmin : min ε 1 ≤ 1 := min_le_right _ _
  have hden : (1 : ℝ) ≤
      (4 * (Fintype.card (OrderedPositiveSubface r) + 1 : ℕ) : ℕ) := by
    push_cast
    have hcard :
        (0 : ℝ) ≤ Fintype.card (OrderedPositiveSubface r) := by
      positivity
    nlinarith
  exact (div_le_self (le_of_lt (lt_min hε zero_lt_one)) hden).trans hmin



theorem sourceBundleRemovalStep_pos (k r : ℕ) :
    0 < sourceBundleRemovalStep k r := by
  unfold sourceBundleRemovalStep
  positivity

theorem sourceBundleRemovalStep_le_one (k r : ℕ) :
    sourceBundleRemovalStep k r ≤ 1 := by
  unfold sourceBundleRemovalStep
  apply (div_le_one (by positivity)).2
  push_cast
  have hr : (0 : ℝ) ≤ r := by positivity
  have hH : (0 : ℝ) ≤ sourceBundleRemovalHorizon k r := by
    positivity
  nlinarith [mul_nonneg hr hH]

theorem sourceBundleRemovalKappa_pos (k r : ℕ) :
    0 < sourceBundleRemovalKappa k r := by
  unfold sourceBundleRemovalKappa
  exact div_pos (sourceBundleRemovalStep_pos k r) (by norm_num)

theorem sourceBundleRemovalKappa_le_one (k r : ℕ) :
    sourceBundleRemovalKappa k r ≤ 1 := by
  unfold sourceBundleRemovalKappa
  have hstep := sourceBundleRemovalStep_le_one k r
  nlinarith [sourceBundleRemovalStep_pos k r]

theorem four_mul_sourceBundleRemovalKappa_le_step (k r : ℕ) :
    4 * sourceBundleRemovalKappa k r ≤
      sourceBundleRemovalStep k r := by
  unfold sourceBundleRemovalKappa
  nlinarith [sourceBundleRemovalStep_pos k r]

theorem sourceBundleRemovalKappa_sq_le_half_step (k r : ℕ) :
    sourceBundleRemovalKappa k r ^ 2 ≤
      sourceBundleRemovalStep k r / 2 := by
  unfold sourceBundleRemovalKappa
  have hpos := sourceBundleRemovalStep_pos k r
  have hone := sourceBundleRemovalStep_le_one k r
  nlinarith [sq_nonneg (sourceBundleRemovalStep k r)]



theorem sourceBundleRemovalStep_total_le_one (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r ≤ 1 :=
  (sourceBundleRemovalStep_total_le_quarter k r).trans (by norm_num)

theorem sourceBundleRemovalStep_total_lt_half (k r : ℕ) :
    (r : ℝ) * (sourceBundleRemovalHorizon k r : ℝ) *
        sourceBundleRemovalStep k r < 1 / 2 :=
  (sourceBundleRemovalStep_total_le_quarter k r).trans_lt (by norm_num)

/-! ## A uniform count threshold from the bounded scale ceiling -/



theorem sourceBundleRemovalCountThreshold_pos
    {δ : ℝ} (hδ : 0 < δ) (k r ceiling : ℕ) :
    0 < sourceBundleRemovalCountThreshold k r ceiling δ := by
  unfold sourceBundleRemovalCountThreshold
  exact mul_pos (by norm_num)
    (pow_pos (sourceBundleDensity_pos hδ ceiling) _)

/-! ## End-to-end source-full ordered removal -/



end Wikipedia.SzemeredisTheorem

end
/-!
# Source-full bundle-counting removal assembly

This file joins the ambient-independent source-full regularity plan to the
rankwise bundle-counting theorem and the source-full bad-base deletion family.
The selected regularity scale is clipped to the finite rank horizon.  Since
the selected scales decrease with rank while `sourceBundleDensity` decreases
with its scale, the resulting density schedule increases with rank; hence its
bundle prefix floor is exactly its rank-zero value.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Ambient-independent scalar budgets -/
/-! ## A uniform count threshold from the bounded scale ceiling -/
/-! ## End-to-end source-full ordered removal -/

open Wikipedia.SzemeredisTheorem in
/-- Tao's source-full hierarchy, the rankwise bundle-counting envelope, and
source-full bad-base cleaning prove uniform ordered removal at every positive
rank. -/
theorem solution
    (k n : ℕ) (hrank : n + 1 ≤ k) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ε hε
  let r : ℕ := n + 1
  let edgeBound : ℕ :=
    (orderedConfigurationInitialBundle k r).edges.card
  let N : ℕ := sourceBundleRemovalHorizon k r
  let δ : ℝ := sourceBundleRemovalDensityBudget ε r
  let step : ℝ := sourceBundleRemovalStep k r
  let κ : ℝ := sourceBundleRemovalKappa k r
  have hδ : 0 < δ := by
    exact sourceBundleRemovalDensityBudget_pos hε r
  have hδ_one : δ ≤ 1 := by
    exact sourceBundleRemovalDensityBudget_le_one hε r
  have hstep : 0 < step := by
    exact sourceBundleRemovalStep_pos k r
  have hκ : 0 < κ := by
    exact sourceBundleRemovalKappa_pos k r
  have hκ_one : κ ≤ 1 := by
    exact sourceBundleRemovalKappa_le_one k r
  have hκ_step : 4 * κ ≤ step := by
    exact four_mul_sourceBundleRemovalKappa_le_step k r
  have hκ_sq : κ ^ 2 ≤ step / 2 := by
    exact sourceBundleRemovalKappa_sq_le_half_step k r
  obtain ⟨Q, hQ⟩ :=
    exists_sourceBundleRemovalGrowthCoefficient
      hδ hδ_one hκ hκ_one N
  let F : NatGrowthFunction := sourceBundleRemovalGrowth Q N
  let initialBound : Fin (r + 1) → ℕ := fun _ => 2
  let S : SourceFullCoarseTargetSchedule.Bounded
      k r initialBound F 0 :=
    Classical.choice
      (SourceFullCoarseTargetSchedule.bounded_nonempty
        k r initialBound F 0)
  let c : ℝ :=
    sourceBundleRemovalCountThreshold k r S.ceiling δ
  have hc : 0 < c := by
    exact sourceBundleRemovalCountThreshold_pos hδ k r S.ceiling
  refine ⟨c, hc, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty H hcount
  let initial : OrderedPartitionComplex G k r :=
    orderedPatternInitialComplex H
  obtain ⟨Cbounded⟩ :=
    S.certificate_nonempty initial (by
      intro q e
      exact complexity_orderedPatternInitialComplex_le_two H q e)
  let C := Cbounded.toSourceFull
  let P : OrderedCoarseFineComplex G k r :=
    C.regularity.toCoarseFine
  let α : ℕ → ℝ := sourceBundleRankwiseDensity δ C.scale
  let β : ℕ → ℝ := sourceBundleRankwiseDefect δ κ N C.scale
  let μ : ℕ → ℝ := bundleRankwiseDensityFloor α
  let τ : ℝ := sourceFullCommonTolerance F C.scale
  let E : ℕ → ℕ → ℝ :=
    bundleRankwiseEnvelopeError α β μ τ
  let D : OrderedPattern.DeletionFamily (G := G) k r :=
    P.sourceFullBadBaseDeletionFamily α β
  have hα : ∀ d, 0 < α d := by
    intro d
    exact sourceBundleRankwiseDensity_pos hδ C.scale d
  have hα_one : ∀ d, α d ≤ 1 := by
    intro d
    exact sourceBundleRankwiseDensity_le_one hδ.le hδ_one C.scale d
  have hβ : ∀ d, 0 ≤ β d := by
    intro d
    exact sourceBundleRankwiseDefect_nonneg δ κ N C.scale d
  have hβ_pos : ∀ d, 0 < β d := by
    intro d
    unfold β sourceBundleRankwiseDefect
    exact sq_pos_of_pos
      (sourceBundleDefectScale_pos hδ hκ N _)
  have hτ : 0 ≤ τ := by
    exact (sourceFullCommonTolerance_pos F C.scale).le
  have hscale : Antitone C.scale := C.scale_antitone
  have henvelopeRaw :=
    sourceBundleRankwiseEnvelope_and_error_lt_half
      (r := r) (edgeBound := edgeBound) (Q := Q)
      hδ hδ_one hκ hstep.le hκ_step hκ_sq
      (by
        simpa [step, N, edgeBound, sourceBundleRemovalHorizon] using
          sourceBundleRemovalStep_total_le_one k r)
      (by
        simpa [step, N, edgeBound, sourceBundleRemovalHorizon] using
          sourceBundleRemovalStep_total_lt_half k r)
      (by simpa [N, edgeBound, sourceBundleRemovalHorizon] using hQ)
      C.scale hscale
  have henvelope : IsBundleCountingEnvelope α β μ τ E := by
    simpa [α, β, μ, τ, E, F, N, edgeBound,
      sourceBundleRemovalHorizon] using henvelopeRaw.1
  have herror : E r edgeBound < 1 / 2 := by
    simpa [α, β, μ, τ, E, F, N, edgeBound,
      sourceBundleRemovalHorizon] using henvelopeRaw.2
  have hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ) := by
    simpa [P, τ] using
      C.isFullyMixedPreliminaryOrderedRegular_common
  have hthreshold :
      c ≤ (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) := by
    have hfloor : 0 ≤ sourceBundleDensity δ S.ceiling :=
      (sourceBundleDensity_pos hδ S.ceiling).le
    have hpoint : ∀ e : PositiveOrderedFace k r,
        sourceBundleDensity δ S.ceiling ≤ α e.rank := by
      intro e
      unfold α sourceBundleRankwiseDensity
      apply sourceBundleDensity_antitone hδ.le
      exact
        (hscale (Fin.zero_le _)).trans
          Cbounded.scale_zero_le_ceiling
    have hprod :
        sourceBundleDensity δ S.ceiling ^
            Fintype.card (PositiveOrderedFace k r) ≤
          ∏ e : PositiveOrderedFace k r, α e.rank := by
      calc
        sourceBundleDensity δ S.ceiling ^
              Fintype.card (PositiveOrderedFace k r) =
            ∏ _e : PositiveOrderedFace k r,
              sourceBundleDensity δ S.ceiling := by simp
        _ ≤ ∏ e : PositiveOrderedFace k r, α e.rank := by
          apply Finset.prod_le_prod
          · intro e _he
            exact hfloor
          · intro e _he
            exact hpoint e
    simpa [c, sourceBundleRemovalCountThreshold] using
      (mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hgoodCount :
      ∀ A : ClosedOrderedAtomConfiguration G k r P.coarse,
        A.IsSourceFullMixedGood P α β →
          c ≤ fullConfigurationCount A := by
    intro A hgood
    exact hthreshold.trans
      (half_rankwiseDensityProduct_le_fullConfigurationCount_of_rankBound
        P A α β μ τ E hα hα_one hβ hτ hgood hregular
        henvelope (by simpa [edgeBound] using herror))
  have hinitial :
      P.coarse.Refines (orderedPatternInitialComplex H) := by
    simpa [P, initial,
      CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine] using
        C.regularity.coarse_refines_initial
  have hcover : H.IsCover D := by
    exact
      sourceFullBadBaseDeletionFamily_isCover_of_sourceFullMixedGood_count
        (by simpa [r] using hrank) H P hinitial α β c hcount hgoodCount
  refine ⟨D, hcover, ?_⟩
  intro e
  have hbase :=
    P.faceDeletionDensity_sourceFullBadBaseDeletionFamily_le
      α β (fun j => (hα (j + 1)).le) (fun j => hβ_pos (j + 1)) e
  calc
    OrderedPattern.faceDeletionDensity D e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1)) := by
      simpa [D] using hbase
    _ ≤ ∑ _q : OrderedPositiveSubface r, (δ + δ) := by
      apply Finset.sum_le_sum
      intro q _hq
      have hd : q.1.1 + 1 ≤ r := by omega
      have hselected :
          sourceBundleSelectedScale C.scale (q.1.1 + 1) =
            C.scale q.1.succ := by
        calc
          sourceBundleSelectedScale C.scale (q.1.1 + 1) =
              C.scale
                ⟨q.1.1 + 1, Nat.lt_succ_iff.mpr hd⟩ :=
            sourceBundleSelectedScale_of_le C.scale hd
          _ = C.scale q.1.succ := by
            apply congrArg C.scale
            exact Fin.ext rfl
      have hcomplexity :
          FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) ≤
            C.scale q.1.succ := by
        simpa [P,
          CoarseTargetOrderedComplexRegularityCertificate.toCoarseFine] using
          C.coarse_complexity q.1.succ (q.2.trans e)
      have hlow :
          (FacePartition.complexity
              (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                α (q.1.1 + 1) ≤ δ := by
        calc
          (FacePartition.complexity
                (P.coarse.partition q.1.succ (q.2.trans e)) : ℝ) *
                  α (q.1.1 + 1) ≤
              (C.scale q.1.succ : ℝ) * α (q.1.1 + 1) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr hcomplexity) (hα _).le
          _ = (C.scale q.1.succ : ℝ) *
                sourceBundleDensity δ (C.scale q.1.succ) := by
            simp [α, sourceBundleRankwiseDensity, hselected]
          _ ≤ δ := mul_sourceBundleDensity_le hδ.le _
      have hfaceLayer :
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) ≤
            P.coarseUpperLayerAtomEnergyGap q.1 := by
        rw [P.coarseUpperLayerAtomEnergyGap_eq_sum_face q.1]
        exact Finset.single_le_sum
          (fun f _ => P.coarseUpperFaceAtomEnergyGap_nonneg q.1 f)
          (Finset.mem_univ (q.2.trans e))
      have hlayer :
          P.coarseUpperLayerAtomEnergyGap q.1 ≤
            sourceFullRankGap F C.scale q.1 := by
        simpa [P] using C.rank_gap_le q.1
      have hdefect :
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤ δ := by
        calc
          P.coarseUpperFaceAtomEnergyGap q.1 (q.2.trans e) /
                β (q.1.1 + 1) ≤
              sourceFullRankGap F C.scale q.1 /
                β (q.1.1 + 1) :=
            div_le_div_of_nonneg_right
              (hfaceLayer.trans hlayer) (hβ _)
          _ =
              (1 /
                  (sourceBundleRemovalGrowth Q N
                    (C.scale q.1.succ) : ℝ) ^ 2) /
                sourceBundleDefectScale δ κ N
                    (C.scale q.1.succ) ^ 2 := by
            simp [F, sourceFullRankGap, β,
              sourceBundleRankwiseDefect, hselected]
          _ ≤ δ :=
            sourceFullRankGap_div_sourceBundleDefectScale_sq_le
              hδ hκ hQ (C.scale q.1.succ)
      exact add_le_add hlow hdefect
    _ = (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (δ + δ) := by
      simp [mul_add]
    _ ≤ ε := by
      simpa [δ, r] using
        card_mul_two_sourceBundleRemovalDensityBudget_le hε (n + 1)
