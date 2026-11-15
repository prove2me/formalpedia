-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HasProjectedMajorantMoments.abs_mean_projectedDifference_mul_excess_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:40:00.810596+00:00
-- url     : https://prove2.me/submissions/25c70539-8720-4c12-9a0d-16a1fc9f8e7a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_GeneralRelativeSimplexStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedFaceCutClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingCertificate
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoder
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderTerminal
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingHeterogeneousMask
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingInduction
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearFormsCS
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
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
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_sub_one_sq_eq

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Finite Cauchy--Schwarz elimination

This file records the normalized finite Cauchy--Schwarz step used in
iterated linear-forms arguments.  A bounded factor depending only on the
outer variables can be removed after squaring, at the cost of duplicating
the inner variable.
-/

namespace Wikipedia.SzemeredisTheorem







/-- Jensen/Cauchy--Schwarz for the square of a normalized finite mean. -/
theorem mean_square_le_mean_square
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) :
    mean f ^ 2 ≤ mean (fun x => f x ^ 2) := by
  have h :=
    Finset.expect_mul_sq_le_sq_mul_sq
      Finset.univ f (fun _ : Ω => (1 : ℝ))
  simpa [mean] using h









end Wikipedia.SzemeredisTheorem

end

section


/-!
# Finite analytic lemmas for densification

This file isolates the elementary projected-majorant estimates used in one
step of Conlon--Fox--Zhao densification.  It does not state a relative
counting theorem.

If a nonnegative finite majorant `ν` has first and second normalized moments
within `η` of one, then

```
mean (fun x => |ν x - 1|) ≤ √(3 * η).
```

For `0 ≤ g ≤ ν`, truncating `g` pointwise at one produces a `[0,1]`-valued
function.  Its `L¹` loss, and its loss in any pairing against a unit-bounded
factor, are bounded first by the mean excess `max (ν - 1) 0`, and hence by
the same square-root moment bound.  The final section records pointwise and
averaged product-perturbation inequalities used to package the remaining
bounded factors in a densification step.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Projected-majorant moments -/





namespace HasProjectedMajorantMoments

/-- First and second moment errors at most `η` give centered second moment at
most `3 * η`. -/
theorem centeredSecondMoment_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν : Ω → ℝ} {η : ℝ}
    (h : HasProjectedMajorantMoments ν η) :
    mean (fun x => (ν x - 1) ^ 2) ≤ 3 * η := by
  have hfirstLower : 1 - η ≤ mean ν := by
    have hneg := (abs_le.mp h.firstMoment_close).1
    linarith
  have hsecondUpper :
      mean (fun x => ν x ^ 2) ≤ 1 + η := by
    have hpos := (abs_le.mp h.secondMoment_close).2
    linarith
  rw [mean_sub_one_sq_eq]
  linarith

/-- Cauchy--Schwarz converts the centered second-moment estimate into a
squared `L¹` estimate. -/
theorem centeredAbsMean_sq_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν : Ω → ℝ} {η : ℝ}
    (h : HasProjectedMajorantMoments ν η) :
    (mean (fun x => |ν x - 1|)) ^ 2 ≤ 3 * η := by
  calc
    (mean (fun x => |ν x - 1|)) ^ 2 ≤
        mean (fun x => |ν x - 1| ^ 2) :=
      mean_square_le_mean_square _
    _ = mean (fun x => (ν x - 1) ^ 2) := by
      apply congrArg mean
      funext x
      exact sq_abs _
    _ ≤ 3 * η :=
      h.centeredSecondMoment_le

/-- Explicit square-root form of the projected-majorant `L¹` bound. -/
theorem centeredAbsMean_le_sqrt
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {ν : Ω → ℝ} {η : ℝ}
    (h : HasProjectedMajorantMoments ν η) :
    mean (fun x => |ν x - 1|) ≤ Real.sqrt (3 * η) := by
  apply
    (Real.le_sqrt
      (mean_nonneg fun x => abs_nonneg (ν x - 1))
      (mul_nonneg (by norm_num) h.error_nonneg)).2
  exact h.centeredAbsMean_sq_le

end HasProjectedMajorantMoments

/-! ## Truncation at one -/













theorem truncateAtOne_le
    {Ω : Type*} (g : Ω → ℝ) (x : Ω) :
    truncateAtOne g x ≤ g x :=
  min_le_left _ _





/-- Excess above one is monotone in the underlying function. -/
theorem excessAboveOne_mono
    {Ω : Type*} {f g : Ω → ℝ}
    (hfg : ∀ x, f x ≤ g x) (x : Ω) :
    excessAboveOne f x ≤ excessAboveOne g x := by
  exact max_le_max (sub_le_sub_right (hfg x) 1) le_rfl

/-- Excess above one is bounded by centered absolute value. -/
theorem excessAboveOne_le_abs_sub_one
    {Ω : Type*} (f : Ω → ℝ) (x : Ω) :
    excessAboveOne f x ≤ |f x - 1| := by
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- Truncation removes exactly the positive excess above one. -/
theorem sub_truncateAtOne_eq_excessAboveOne
    {Ω : Type*} (g : Ω → ℝ) (x : Ω) :
    g x - truncateAtOne g x = excessAboveOne g x := by
  by_cases hx : g x ≤ 1
  · simp [truncateAtOne, excessAboveOne, min_eq_left hx,
      max_eq_right (sub_nonpos.mpr hx)]
  · have hx' : 1 ≤ g x := le_of_not_ge hx
    simp [truncateAtOne, excessAboveOne, min_eq_right hx',
      max_eq_left (sub_nonneg.mpr hx')]

/-- Absolute truncation loss is the same positive excess. -/
theorem abs_sub_truncateAtOne_eq_excessAboveOne
    {Ω : Type*} (g : Ω → ℝ) (x : Ω) :
    |g x - truncateAtOne g x| = excessAboveOne g x := by
  rw [abs_of_nonneg
    (sub_nonneg.mpr (truncateAtOne_le g x))]
  exact sub_truncateAtOne_eq_excessAboveOne g x

/-- If `g ≤ ν`, pointwise truncation loss is charged to the excess of the
majorant `ν` above one. -/
theorem abs_sub_truncateAtOne_le_excessAboveOne
    {Ω : Type*} {g ν : Ω → ℝ}
    (hgν : ∀ x, g x ≤ ν x) (x : Ω) :
    |g x - truncateAtOne g x| ≤ excessAboveOne ν x := by
  rw [abs_sub_truncateAtOne_eq_excessAboveOne]
  exact excessAboveOne_mono hgν x





namespace HasProjectedMajorantMoments







end HasProjectedMajorantMoments

/-! ## Pairing and product perturbations -/





namespace HasProjectedMajorantMoments



end HasProjectedMajorantMoments











namespace HasProjectedMajorantMoments



end HasProjectedMajorantMoments

end Wikipedia.SzemeredisTheorem

end
/-!
# Active-majorant recurrence for relative simplex counting

The weighted Cauchy--Schwarz decoder supplies a certificate when both
copies of every active incident face use the same AP majorant.  Relative
counting also produces two cross terms: one omitted-coordinate copy is
sparse and the other is bounded by one.  This file separates those two
issues exactly.

First, the completed homogeneous certificate is transported from AP
pullback factors to arbitrary weighted-simplex edge factors.  This is
possible because a `HasCFZCertificate` depends on the core and designated
majorants, but not on the particular nonnegative factors below them.

The second part packages the active-cardinality bookkeeping and the
one-step counting recurrence.  Its only extra strong-linear-forms input is
the pair of genuinely mixed-copy centered correlations.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## Factor-independence of structural CFZ certificates -/
/-! ## Arbitrary simplex factors under homogeneous AP majorants -/
/-! ## Active-face cardinality and the comparison invariant -/
/-! ## Replacing one canonical edge by a whole-face function -/
/-! ## The exact mixed-copy strong-linear-forms interface -/
/-! ## Direct cut term and projected pointwise bounds -/
/-! ## Truncation and the lower-cardinality quadratic term -/

open Wikipedia.SzemeredisTheorem.HasProjectedMajorantMoments in
/-- The part of the projected square lost by truncating its sparse
projection is controlled solely by the first two moments of the projected
majorant. -/
theorem solution
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {M A B : Ω → ℝ} {η : ℝ}
    (hM : HasProjectedMajorantMoments M η)
    (hA0 : ∀ x, 0 ≤ A x)
    (hAM : ∀ x, A x ≤ M x)
    (hB0 : ∀ x, 0 ≤ B x)
    (hB1 : ∀ x, B x ≤ 1) :
    |mean (fun x =>
        (A x - B x) *
          (A x - truncateAtOne A x))| ≤
      3 * η + 2 * Real.sqrt (3 * η) := by
  have hpoint :
      ∀ x,
        |(A x - B x) *
            (A x - truncateAtOne A x)| ≤
          (M x + 1) * |M x - 1| := by
    intro x
    rw [abs_mul]
    have hleft : |A x - B x| ≤ M x + 1 := by
      calc
        |A x - B x| ≤ |A x| + |B x| := abs_sub _ _
        _ = A x + B x := by
          rw [abs_of_nonneg (hA0 x),
            abs_of_nonneg (hB0 x)]
        _ ≤ M x + 1 := add_le_add (hAM x) (hB1 x)
    have hright :
        |A x - truncateAtOne A x| ≤
          |M x - 1| :=
      (abs_sub_truncateAtOne_le_excessAboveOne
        hAM x).trans
        (excessAboveOne_le_abs_sub_one M x)
    exact mul_le_mul hleft hright
      (abs_nonneg _) (by linarith [hM.nonneg x])
  have hmajorantPoint :
      ∀ x,
        (M x + 1) * |M x - 1| ≤
          (M x - 1) ^ 2 +
            2 * |M x - 1| := by
    intro x
    let d := M x - 1
    have hd :
        d * |d| ≤ d ^ 2 := by
      by_cases hd0 : 0 ≤ d
      · rw [abs_of_nonneg hd0]
        simp [pow_two]
      · have hdle : d ≤ 0 := le_of_not_ge hd0
        exact
          (mul_nonpos_of_nonpos_of_nonneg
            hdle (abs_nonneg d)).trans (sq_nonneg d)
    change
      (M x + 1) * |d| ≤ d ^ 2 + 2 * |d|
    calc
      (M x + 1) * |d| =
          d * |d| + 2 * |d| := by
        dsimp [d]
        ring
      _ ≤ d ^ 2 + 2 * |d| :=
        add_le_add hd le_rfl
  calc
    |mean (fun x =>
        (A x - B x) *
          (A x - truncateAtOne A x))| ≤
        mean (fun x =>
          |(A x - B x) *
            (A x - truncateAtOne A x)|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun x =>
          (M x + 1) * |M x - 1|) :=
      mean_mono hpoint
    _ ≤ mean (fun x =>
          (M x - 1) ^ 2 +
            2 * |M x - 1|) :=
      mean_mono hmajorantPoint
    _ =
        mean (fun x => (M x - 1) ^ 2) +
          2 * mean (fun x => |M x - 1|) := by
      rw [mean_add, mean_smul]
    _ ≤ 3 * η + 2 * Real.sqrt (3 * η) :=
      add_le_add
        hM.centeredSecondMoment_le
        (mul_le_mul_of_nonneg_left
          hM.centeredAbsMean_le_sqrt (by norm_num))
