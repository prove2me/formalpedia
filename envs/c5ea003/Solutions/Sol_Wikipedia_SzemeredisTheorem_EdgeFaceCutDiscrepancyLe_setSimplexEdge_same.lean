-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.EdgeFaceCutDiscrepancyLe.setSimplexEdge_same
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:36:30.846339+00:00
-- url     : https://prove2.me/submissions/373962c9-1c31-457e-96ed-5b092db42e5a

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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators















@[simp]
theorem mean_zero {α : Type*} [Fintype α] :
    mean (fun _ : α => (0 : ℝ)) = 0 := by
  simp [mean]



















end Wikipedia.SzemeredisTheorem

end

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







theorem FaceCutDiscrepancyLe.refl
    {G : Type*} [Fintype G] {r : ℕ}
    (f : (Fin r → G) → ℝ) :
    FaceCutDiscrepancyLe f f 0 := by
  intro u hu
  simp [faceCutDifferenceCorrelation]

theorem FaceCutDiscrepancyLe.mono
    {G : Type*} [Fintype G] {r : ℕ}
    {f g : (Fin r → G) → ℝ} {ε ε' : ℝ}
    (h : FaceCutDiscrepancyLe f g ε)
    (hε : ε ≤ ε') :
    FaceCutDiscrepancyLe f g ε' :=
  fun u hu => (h u hu).trans hε



/-- The constant-one lower-face tests show that face-cut discrepancy
controls the difference of normalized means. -/
theorem FaceCutDiscrepancyLe.abs_mean_sub_le
    {G : Type*} [Fintype G] [Nonempty G] {r : ℕ}
    {f g : (Fin r → G) → ℝ} {ε : ℝ}
    (h : FaceCutDiscrepancyLe f g ε) :
    |mean f - mean g| ≤ ε := by
  have hone :=
    h (fun _ : Fin r =>
      fun _ : Fin (r - 1) → G => (1 : ℝ))
      isBoundedCutTest_one
  simpa [faceCutDifferenceCorrelation, cutTestProduct,
    ← mean_sub] using hone

theorem FaceCutDiscrepancyLe.epsilon_nonneg
    {G : Type*} [Fintype G] [Nonempty G] {r : ℕ}
    {f g : (Fin r → G) → ℝ} {ε : ℝ}
    (h : FaceCutDiscrepancyLe f g ε) :
    0 ≤ ε :=
  (abs_nonneg (mean f - mean g)).trans h.abs_mean_sub_le

/-! ## Edgewise discrepancy for arbitrary weighted simplices -/













/-! ## Bridge from the existing AP cut discrepancy -/









/-! ## Projected endpoint comparisons -/















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
theorem canonicalEdgeFunction_setSimplexEdge_selected
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    canonicalEdgeFunction (setSimplexEdge H j f) j = f := by
  funext y
  simp [canonicalEdgeFunction]

theorem canonicalEdgeFunction_setSimplexEdge_other
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j i : Fin (n + 1))
    (f : (Fin n → G) → ℝ)
    (hij : i ≠ j) :
    canonicalEdgeFunction (setSimplexEdge H j f) i =
      canonicalEdgeFunction H i := by
  funext y
  simp [canonicalEdgeFunction,
    setSimplexEdge_other H j i f hij]

















/-! ## The exact mixed-copy strong-linear-forms interface -/





















/-! ## Direct cut term and projected pointwise bounds -/















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

/-- Replacing the same edge on both sides preserves edgewise face-cut
discrepancy. -/
theorem solution
    {G : Type*} [Fintype G] [Nonempty G] {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (hcut : EdgeFaceCutDiscrepancyLe H K ε)
    (j : Fin (n + 1))
    (f : (Fin n → G) → ℝ) :
    EdgeFaceCutDiscrepancyLe
      (setSimplexEdge H j f)
      (setSimplexEdge K j f) ε := by
  intro i
  by_cases hij : i = j
  · subst i
    rw [canonicalEdgeFunction_setSimplexEdge_selected,
      canonicalEdgeFunction_setSimplexEdge_selected]
    exact
      (FaceCutDiscrepancyLe.refl f).mono
        (hcut j).epsilon_nonneg
  · rw [canonicalEdgeFunction_setSimplexEdge_other
      H j i f hij,
      canonicalEdgeFunction_setSimplexEdge_other
      K j i f hij]
    exact hcut i
