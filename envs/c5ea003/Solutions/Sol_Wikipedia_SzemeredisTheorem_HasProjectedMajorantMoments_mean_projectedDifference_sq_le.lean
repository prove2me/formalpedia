-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HasProjectedMajorantMoments.mean_projectedDifference_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:45:55.849724+00:00
-- url     : https://prove2.me/submissions/5323b4b3-4389-47fe-bb3a-de78843271f2

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HasProjectedMajorantMoments_abs_mean_projectedDifference_mul_excess_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MaskedSimplexComparisonLe_abs_mean_projectedDifference_mul_truncatedDifference_le

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
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl















end Wikipedia.SzemeredisTheorem

end

section


/-!
# Heterogeneous AP-simplex densification states

The one-colour calculation in `RelativeDensification` uses one common
function on every non-distinguished AP face.  This file performs the same
calculation for a family of face weights `g i`.  For a chosen colour `j`,
the product of all other colours is averaged over the missing `j`
coordinate, then truncated at one on the actual deleted-face space
`Fin n → ZMod N`.

The final section packages the full simplex count and the resulting
lower-arity pairing as two different constructors of one payload type.  In
particular, the projected state is not falsely identified with another
`(n + 1)`-colour AP simplex.  It records the bounded surrogate on its real
domain and separately transports all untouched pointwise majorant bounds
along `j.succAbove`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Heterogeneous AP face systems -/





@[simp]
theorem apHeterogeneousSimplexSystem_edge
    (n N : ℕ) (g : APFaceWeightFamily n N)
    (i : Fin (n + 1))
    (x : DeletedVector
      (fun _ : Fin (n + 1) => ZMod N) i) :
    (apHeterogeneousSimplexSystem n N g).edgeWeight i x =
      g i (apSimplexForm (n + 1) N i x) :=
  rfl



















/-! ## Projection bounds -/













/-! ## Exact heterogeneous count and pairing -/













/-! ## A concrete full-to-projected state transition -/































namespace RelativeDensificationIteration



end RelativeDensificationIteration











end Wikipedia.SzemeredisTheorem

end

section


/-!
# A relative densification step for arbitrary simplex edge functions

The AP-specific transition works with edge functions pulled back from one
function on `ZMod N`.  After re-embedding a projected pairing, however, the
only nonconstant edge is an arbitrary function on its whole deleted-face
space.  This file formulates projection and truncation directly for a
`WeightedSimplexSystem`.

For a fully bounded system the constant-one simplex is a pointwise
majorant.  Its projected majorant is identically one, so its first and
second moment errors are exactly zero.  The resulting generic transition
therefore has zero loss.  In particular it consumes the selectable endpoint
constructed in `RecursiveRelativeCount`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Projection of an arbitrary weighted simplex -/















/-! ## Pointwise bounds and projected domination -/



theorem generalSimplexIncidentProduct_nonneg
    {G : Type*} {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j : Fin (n + 1)}
    (h : GeneralSimplexUntouchedBounds H K j)
    (a : G) (y : Fin n → G) :
    0 ≤ generalSimplexIncidentProduct H j a y :=
  Finset.prod_nonneg fun t _ => (h t _).1

theorem generalSimplexIncidentProduct_mono
    {G : Type*} {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j : Fin (n + 1)}
    (h : GeneralSimplexUntouchedBounds H K j)
    (a : G) (y : Fin n → G) :
    generalSimplexIncidentProduct H j a y ≤
      generalSimplexIncidentProduct K j a y := by
  unfold generalSimplexIncidentProduct
  exact Finset.prod_le_prod
    (fun t _ => (h t _).1)
    (fun t _ => (h t _).2)

theorem generalSimplexProjectedWeight_nonneg
    {G : Type*} [Fintype G] {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j : Fin (n + 1)}
    (h : GeneralSimplexUntouchedBounds H K j)
    (y : Fin n → G) :
    0 ≤ generalSimplexProjectedWeight H j y :=
  mean_nonneg fun a =>
    generalSimplexIncidentProduct_nonneg h a y

theorem generalSimplexProjectedWeight_mono
    {G : Type*} [Fintype G] {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {j : Fin (n + 1)}
    (h : GeneralSimplexUntouchedBounds H K j)
    (y : Fin n → G) :
    generalSimplexProjectedWeight H j y ≤
      generalSimplexProjectedWeight K j y :=
  mean_mono fun a =>
    generalSimplexIncidentProduct_mono h a y





/-! ## The generic analytic transition -/



/-! ## The constant-one majorant -/





@[simp]
theorem generalSimplexIncidentProduct_one
    {G : Type*} {n : ℕ}
    (j : Fin (n + 1))
    (a : G) (y : Fin n → G) :
    generalSimplexIncidentProduct
      (oneWeightedSimplexSystem G n) j a y = 1 := by
  simp [generalSimplexIncidentProduct,
    oneWeightedSimplexSystem]

@[simp]
theorem generalSimplexProjectedWeight_one
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    (j : Fin (n + 1)) :
    generalSimplexProjectedWeight
      (oneWeightedSimplexSystem G n) j =
        fun _ => 1 := by
  funext y
  simp [generalSimplexProjectedWeight]



/-- Every fully bounded simplex is dominated, on its untouched edges, by
the constant-one simplex. -/
theorem EdgeWeightsInUnitInterval.generalSimplexUntouchedBounds_one
    {G : Type*} {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) :
    GeneralSimplexUntouchedBounds H
      (oneWeightedSimplexSystem G n) j := by
  intro t x
  exact hH (j.succAbove t) x



/-! ## Generic full and projected states -/

























/-! ## Consuming the recursive selectable endpoint -/















end Wikipedia.SzemeredisTheorem

end

section


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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Factor-independence of structural CFZ certificates -/

namespace MajorizedCutSystem



end MajorizedCutSystem

/-! ## Arbitrary simplex factors under homogeneous AP majorants -/





















/-! ## Active-face cardinality and the comparison invariant -/























/-! ## Replacing one canonical edge by a whole-face function -/



























/-! ## The exact mixed-copy strong-linear-forms interface -/





















/-! ## Direct cut term and projected pointwise bounds -/











/-- Full edge majorization supplies the untouched-edge form used by the
generic projection API. -/
theorem SimplexEdgeMajorizedBy.generalSimplexUntouchedBounds
    {G : Type*} {n : ℕ}
    {H M : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (h : SimplexEdgeMajorizedBy H M)
    (j : Fin (n + 1)) :
    GeneralSimplexUntouchedBounds H M j :=
  fun t x => h (j.succAbove t) x

/-- A projected weight of a fully bounded simplex lies in `[0,1]`. -/
theorem generalSimplexProjectedWeight_mem_unitInterval
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    {K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1))
    (y : Fin n → G) :
    0 ≤ generalSimplexProjectedWeight K j y ∧
      generalSimplexProjectedWeight K j y ≤ 1 := by
  have hrest := hK.generalSimplexUntouchedBounds_one j
  constructor
  · exact generalSimplexProjectedWeight_nonneg hrest y
  · calc
      generalSimplexProjectedWeight K j y ≤
          generalSimplexProjectedWeight
            (oneWeightedSimplexSystem G n) j y :=
        generalSimplexProjectedWeight_mono hrest y
      _ = 1 := by
        rw [generalSimplexProjectedWeight_one]

/-! ## Truncation and the lower-cardinality quadratic term -/







/-! ## One active-face recurrence -/











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
/-- Projected moments and the lower-active-count comparison give an
ordinary `L²` bound for the difference of the sparse and dense
projections.

The first summand is the part above the truncation level one.  The second
summand is a genuine lower-mask simplex count, because the common
truncated projection can be inserted as the selected edge. -/
theorem solution
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    {active : Fin (n + 1) → Bool}
    {η cutError countError : ℝ}
    (j : Fin (n + 1))
    (hMoments :
      HasProjectedMajorantMoments
        (generalSimplexProjectedWeight
          (apMaskedSimplexMajorantSystem n N ν active) j) η)
    (hlower :
      MaskedSimplexComparisonLe n N ν
        (deactivateFace active j) cutError countError)
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N)}
    (hH :
      SimplexEdgeMajorizedBy H
        (apMaskedSimplexMajorantSystem n N ν active))
    (hK : EdgeWeightsInUnitInterval K)
    (hcut : EdgeFaceCutDiscrepancyLe H K cutError) :
    mean (fun y =>
        (generalSimplexProjectedWeight H j y -
          generalSimplexProjectedWeight K j y) ^ 2) ≤
      3 * η + 2 * Real.sqrt (3 * η) +
        2 * countError := by
  let M :=
    generalSimplexProjectedWeight
      (apMaskedSimplexMajorantSystem n N ν active) j
  let A := generalSimplexProjectedWeight H j
  let B := generalSimplexProjectedWeight K j
  let C := truncateAtOne A
  have hrest :
      GeneralSimplexUntouchedBounds H
        (apMaskedSimplexMajorantSystem n N ν active) j :=
    hH.generalSimplexUntouchedBounds j
  have hA0 : ∀ y, 0 ≤ A y :=
    generalSimplexProjectedWeight_nonneg hrest
  have hAM : ∀ y, A y ≤ M y :=
    generalSimplexProjectedWeight_mono hrest
  have hB :
      ∀ y, 0 ≤ B y ∧ B y ≤ 1 :=
    generalSimplexProjectedWeight_mem_unitInterval hK j
  have hexcess :
      |mean (fun y =>
          (A y - B y) * (A y - C y))| ≤
        3 * η + 2 * Real.sqrt (3 * η) := by
    exact
      hMoments.abs_mean_projectedDifference_mul_excess_le
        hA0 hAM (fun y => (hB y).1) (fun y => (hB y).2)
  have htruncated :
      |mean (fun y =>
          (A y - B y) * (C y - B y))| ≤
        2 * countError := by
    exact
      hlower.abs_mean_projectedDifference_mul_truncatedDifference_le
        j hH hK hcut
  have hexpand :
      mean (fun y => (A y - B y) ^ 2) =
        mean (fun y =>
          (A y - B y) * (A y - C y)) +
        mean (fun y =>
          (A y - B y) * (C y - B y)) := by
    rw [← mean_add]
    apply congrArg mean
    funext y
    ring
  change
    mean (fun y => (A y - B y) ^ 2) ≤
      3 * η + 2 * Real.sqrt (3 * η) +
        2 * countError
  rw [hexpand]
  calc
    mean (fun y =>
          (A y - B y) * (A y - C y)) +
        mean (fun y =>
          (A y - B y) * (C y - B y)) ≤
        |mean (fun y =>
          (A y - B y) * (A y - C y))| +
        |mean (fun y =>
          (A y - B y) * (C y - B y))| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤
        (3 * η + 2 * Real.sqrt (3 * η)) +
          2 * countError :=
      add_le_add hexcess htruncated
    _ =
        3 * η + 2 * Real.sqrt (3 * η) +
          2 * countError := by ring
