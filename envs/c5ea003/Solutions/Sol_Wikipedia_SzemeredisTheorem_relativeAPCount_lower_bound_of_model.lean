-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.relativeAPCount_lower_bound_of_model
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:31:12.220875+00:00
-- url     : https://prove2.me/submissions/2867e8ee-5312-46d2-8f8b-b944cd50cea5

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSzemeredi
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APRemoval
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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedSimplexBridge
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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_sum_fin_succ

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





















































theorem mean_sum_fin_of_pos
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) (h : G → ℝ) :
    mean (fun x : Fin r → G => h (∑ i, x i)) = mean h := by
  cases r with
  | zero => simp at hr
  | succ n => exact mean_sum_fin_succ n h

@[simp]
theorem cutCorrelation_one
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) :
    cutCorrelation r f g
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
    mean (fun x : Fin r → G =>
      f (∑ i, x i) - g (∑ i, x i)) := by
  simp [cutCorrelation]

theorem cutCorrelation_one_eq_mean_sub
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) (f g : G → ℝ) :
    cutCorrelation r f g
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
    mean f - mean g := by
  calc
    cutCorrelation r f g
        (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
      mean (fun x : Fin r → G =>
        f (∑ i, x i) - g (∑ i, x i)) :=
      cutCorrelation_one r f g
    _ = mean (fun z : G => f z - g z) :=
      mean_sum_fin_of_pos hr (fun z => f z - g z)
    _ = mean f - mean g := mean_sub f g

/-- The constant-one tests show that cut discrepancy controls the difference
of the means whenever at least one coordinate is present. -/
theorem CutDiscrepancyLe.abs_mean_sub_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε) (hr : 0 < r) :
    |mean f - mean g| ≤ ε := by
  have hone := h
    (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ))
    (fun _ _ => by norm_num) (fun _ _ => le_rfl)
  simpa [cutCorrelation_one_eq_mean_sub hr f g] using hone

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped Pointwise























theorem IsUnitBounded.nonneg
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, 0 ≤ g x :=
  hg.1

theorem IsUnitBounded.le_one
    {Ω : Type*} {g : Ω → ℝ} (hg : IsUnitBounded g) :
    ∀ x, g x ≤ 1 :=
  hg.2





























































































































end Wikipedia.SzemeredisTheorem

end
/-!
# Quantitative relative Szemerédi assembly

This file composes the parts of transference which do not depend on the
remaining sparse-simplex comparison.

* Cut discrepancy against the constant tests retains the mean of the sparse
  weight in its dense model.
* A uniform weighted Szemerédi theorem gives a positive lower bound for the
  dense model's progression count.
* Any quantitative relative-counting comparison then transfers that lower
  bound back to the sparse weight.

The final theorem plugs in the polynomial dense-model theorem obtained from
the ordinary CFZ linear-forms condition.  Its only unproved analytic input
is named explicitly by `RelativeAPComparisonLe`; no asymptotic or
pseudorandomness assertion is hidden in this module.
-/
open Wikipedia.SzemeredisTheorem
open scoped Polynomial

open Wikipedia.SzemeredisTheorem in
/-- A dense model with enough retained mean and a relative-counting
comparison transfers the weighted Szemerédi lower bound to the sparse
weight. -/
theorem solution
    {r N : ℕ} [NeZero N]
    {ν f g : ZMod N → ℝ}
    {δ denseCount cutError countError : ℝ}
    (hweighted :
      HasWeightedAPCount (r + 2) N δ denseCount)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfν : ∀ x, f x ≤ ν x)
    (hg : IsUnitBounded g)
    (hcut : CutDiscrepancyLe (r + 1) f g cutError)
    (hmean : δ + cutError ≤ mean f)
    (hcomparison :
      RelativeAPComparisonLe
        r N ν cutError countError) :
    denseCount - countError ≤
      cyclicAPCount (r + 2) N f := by
  have hmeanDifference :
      |mean f - mean g| ≤ cutError :=
    hcut.abs_mean_sub_le (Nat.succ_pos r)
  have hgmean : δ ≤ mean g := by
    have hupper := (abs_le.mp hmeanDifference).2
    linarith
  have hdense :
      denseCount ≤ cyclicAPCount (r + 2) N g :=
    hweighted g hg.nonneg hg.le_one hgmean
  have hcountDifference :
      |cyclicAPCount (r + 2) N f -
          cyclicAPCount (r + 2) N g| ≤ countError :=
    hcomparison f g hf0 hfν hg hcut
  have hlower := (abs_le.mp hcountDifference).1
  linarith
