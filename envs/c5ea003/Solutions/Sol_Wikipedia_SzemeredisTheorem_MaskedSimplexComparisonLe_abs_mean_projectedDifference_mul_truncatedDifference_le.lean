-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.MaskedSimplexComparisonLe.abs_mean_projectedDifference_mul_truncatedDifference_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:44:39.200104+00:00
-- url     : https://prove2.me/submissions/5d2df379-a411-46bc-bc34-b4fb385df4e1

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_EdgeFaceCutDiscrepancyLe_setSimplexEdge_same
import Theorems.Thm_Wikipedia_SzemeredisTheorem_generalSimplexCount_eq_projectedPairing
import Theorems.Thm_Wikipedia_SzemeredisTheorem_setSimplexEdge_majorized_deactivateFace

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







end HasProjectedMajorantMoments

/-! ## Truncation at one -/









theorem truncateAtOne_nonneg
    {Ω : Type*} {g : Ω → ℝ}
    (hg : ∀ x, 0 ≤ g x) (x : Ω) :
    0 ≤ truncateAtOne g x :=
  le_min (hg x) zero_le_one

theorem truncateAtOne_le_one
    {Ω : Type*} (g : Ω → ℝ) (x : Ω) :
    truncateAtOne g x ≤ 1 :=
  min_le_right _ _



/-- A nonnegative function becomes `[0,1]`-valued after truncation. -/
theorem truncateAtOne_mem_unitInterval
    {Ω : Type*} {g : Ω → ℝ}
    (hg : ∀ x, 0 ≤ g x) (x : Ω) :
    0 ≤ truncateAtOne g x ∧ truncateAtOne g x ≤ 1 :=
  ⟨truncateAtOne_nonneg hg x, truncateAtOne_le_one g x⟩

















namespace HasProjectedMajorantMoments







end HasProjectedMajorantMoments

/-! ## Pairing and product perturbations -/





namespace HasProjectedMajorantMoments



end HasProjectedMajorantMoments











namespace HasProjectedMajorantMoments



end HasProjectedMajorantMoments

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
# Weak-regularity counting for simplex systems

Each deleted face of a simplex with `n+1` colours is canonically presented as
an ordinary `Fin n → G` tuple.  A family of regularity states therefore gives
a structured simplex system by conditionally averaging every edge weight.

The main result is an exact weak counting lemma.  If every edge residual is
small against lower-face product cuts, then the original and structured
simplex counts differ by at most `(n+1) ε`.  The proof fixes the missing
vertex in one telescoping term; the remaining edge factors become precisely a
bounded cut-test family on the distinguished edge.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem deletedFaceTuple_finTupleToDeletedVector
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (y : Fin n → G) :
    deletedFaceTuple j (finTupleToDeletedVector j y) = y := by
  funext t
  simp [deletedFaceTuple]

















































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



@[simp]
theorem setSimplexEdge_selected
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ)
    (x : DeletedVector
      (fun _ : Fin (n + 1) => G) j) :
    (setSimplexEdge H j f).edgeWeight j x =
      f (deletedFaceTuple j x) := by
  simp [setSimplexEdge]

theorem setSimplexEdge_other
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j i : Fin (n + 1))
    (f : (Fin n → G) → ℝ)
    (hij : i ≠ j)
    (x : DeletedVector
      (fun _ : Fin (n + 1) => G) i) :
    (setSimplexEdge H j f).edgeWeight i x =
      H.edgeWeight i x := by
  simp [setSimplexEdge, hij]





@[simp]
theorem generalSimplexIncidentProduct_setSimplexEdge
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ)
    (a : G) (y : Fin n → G) :
    generalSimplexIncidentProduct
        (setSimplexEdge H j f) j a y =
      generalSimplexIncidentProduct H j a y := by
  unfold generalSimplexIncidentProduct
  apply Fintype.prod_congr
  intro t
  exact setSimplexEdge_other H j
    (j.succAbove t) f (Fin.succAbove_ne j t) _

@[simp]
theorem generalSimplexProjectedWeight_setSimplexEdge
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    generalSimplexProjectedWeight
        (setSimplexEdge H j f) j =
      generalSimplexProjectedWeight H j := by
  funext y
  unfold generalSimplexProjectedWeight
  apply congrArg mean
  funext a
  exact generalSimplexIncidentProduct_setSimplexEdge
    H j f a y

@[simp]
theorem generalSimplexDistinguishedWeight_setSimplexEdge
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    generalSimplexDistinguishedWeight
        (setSimplexEdge H j f) j = f := by
  funext y
  simp [generalSimplexDistinguishedWeight]

/-- Replacing one edge turns the simplex count into the projected weight
paired with the replacement. -/
theorem setSimplexEdge_simplexCount
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    (setSimplexEdge H j f).simplexCount =
      mean (fun y =>
        generalSimplexProjectedWeight H j y * f y) := by
  rw [generalSimplexCount_eq_projectedPairing,
    generalSimplexProjectedWeight_setSimplexEdge,
    generalSimplexDistinguishedWeight_setSimplexEdge]



/-- Replacing one edge of a bounded system by another unit-bounded
function preserves boundedness. -/
theorem setSimplexEdge_unitInterval
    {G : Type*} {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1))
    {f : (Fin n → G) → ℝ}
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) :
    EdgeWeightsInUnitInterval (setSimplexEdge H j f) := by
  intro i x
  by_cases hij : i = j
  · subst i
    simpa using hf (deletedFaceTuple j x)
  · simpa [setSimplexEdge_other H j i f hij] using hH i x



/-- One application of the lower-active-count comparison after replacing
the selected face by a common bounded whole-face function. -/
theorem MaskedSimplexComparisonLe.setSimplexEdge_same
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    {active : Fin (n + 1) → Bool}
    {cutError countError : ℝ}
    (j : Fin (n + 1))
    (hlower :
      MaskedSimplexComparisonLe n N ν
        (deactivateFace active j) cutError countError)
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N)}
    (hH :
      SimplexEdgeMajorizedBy H
        (apMaskedSimplexMajorantSystem n N ν active))
    (hK : EdgeWeightsInUnitInterval K)
    (hcut : EdgeFaceCutDiscrepancyLe H K cutError)
    {f : (Fin n → ZMod N) → ℝ}
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) :
    |(setSimplexEdge H j f).simplexCount -
        (setSimplexEdge K j f).simplexCount| ≤
      countError :=
  hlower
    (setSimplexEdge H j f)
    (setSimplexEdge K j f)
    (setSimplexEdge_majorized_deactivateFace hH j hf)
    (setSimplexEdge_unitInterval hK j hf)
    (hcut.setSimplexEdge_same j f)

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

open Wikipedia.SzemeredisTheorem.MaskedSimplexComparisonLe in
/-- The lower-active-count comparison controls the quadratic pairing of
the projected difference against its bounded truncation difference. -/
theorem solution
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ}
    {active : Fin (n + 1) → Bool}
    {cutError countError : ℝ}
    (j : Fin (n + 1))
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
    |mean (fun y =>
        (generalSimplexProjectedWeight H j y -
          generalSimplexProjectedWeight K j y) *
        (truncateAtOne
            (generalSimplexProjectedWeight H j) y -
          generalSimplexProjectedWeight K j y))| ≤
      2 * countError := by
  let A := generalSimplexProjectedWeight H j
  let B := generalSimplexProjectedWeight K j
  let C := truncateAtOne A
  have hA0 : ∀ y, 0 ≤ A y := by
    intro y
    exact generalSimplexProjectedWeight_nonneg
      (hH.generalSimplexUntouchedBounds j) y
  have hC : ∀ y, 0 ≤ C y ∧ C y ≤ 1 :=
    truncateAtOne_mem_unitInterval hA0
  have hB : ∀ y, 0 ≤ B y ∧ B y ≤ 1 :=
    generalSimplexProjectedWeight_mem_unitInterval hK j
  have hcountC :=
    MaskedSimplexComparisonLe.setSimplexEdge_same
      j hlower hH hK hcut hC
  have hcountB :=
    MaskedSimplexComparisonLe.setSimplexEdge_same
      j hlower hH hK hcut hB
  rw [setSimplexEdge_simplexCount,
    setSimplexEdge_simplexCount] at hcountC hcountB
  change
    |mean (fun y => A y * C y) -
      mean (fun y => B y * C y)| ≤ countError at hcountC
  change
    |mean (fun y => A y * B y) -
      mean (fun y => B y * B y)| ≤ countError at hcountB
  have hexpand :
      mean (fun y => (A y - B y) * (C y - B y)) =
        (mean (fun y => A y * C y) -
          mean (fun y => B y * C y)) -
        (mean (fun y => A y * B y) -
          mean (fun y => B y * B y)) := by
    rw [← mean_sub, ← mean_sub, ← mean_sub]
    apply congrArg mean
    funext y
    ring
  change
    |mean (fun y => (A y - B y) * (C y - B y))| ≤
      2 * countError
  rw [hexpand]
  calc
    |(mean (fun y => A y * C y) -
        mean (fun y => B y * C y)) -
      (mean (fun y => A y * B y) -
        mean (fun y => B y * B y))| ≤
        |mean (fun y => A y * C y) -
          mean (fun y => B y * C y)| +
        |mean (fun y => A y * B y) -
          mean (fun y => B y * B y)| :=
      abs_sub _ _
    _ ≤ countError + countError :=
      add_le_add hcountC hcountB
    _ = 2 * countError := by ring
