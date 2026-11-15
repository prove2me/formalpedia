-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_directProjectedDifference_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:44:13.944326+00:00
-- url     : https://prove2.me/submissions/9d729ff5-21f8-4552-b60b-b9eac50d3849

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

































theorem mean₂_comm {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean₂ f = mean₂ (fun y x => f x y) := by
  exact Finset.expect_comm Finset.univ Finset.univ f

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
# Cut control of arithmetic-progression simplex counts

For one edge in the arithmetic-progression simplex, the remaining edge
weights form a product of deleted-coordinate cut tests.  The distinguished
edge is an automorphic weighted sum when the modulus is coprime to the
relevant factorial.  This file makes that reduction exact and then applies
cut discrepancy edge by edge.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





/-- Replacing a coordinate does not change the deleted vector at that
coordinate. -/
@[simp]
theorem deleteCoordinate_update_same
    {k : ℕ} {G : Type*}
    (x : Fin k → G) (i : Fin k) (a : G) :
    deleteCoordinate (Function.update x i a) i =
      deleteCoordinate x i := by
  funext q
  simp [deleteCoordinate, q.2]

/-- Inserting a replacement into the erased tuple is `Function.update`. -/
theorem insertNth_eraseCoordinate_eq_update
    {n : ℕ} {G : Type*}
    (i : Fin (n + 1)) (a : G) (x : Fin (n + 1) → G) :
    Fin.insertNth i a (eraseCoordinate i x) =
      Function.update x i a := by
  exact Fin.insertNth_removeNth i a x



























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
theorem insertErasedCoordinate_eraseCoordinate
    {G : Type*} {n : ℕ}
    (t : Fin n) (a : G) (y : Fin n → G) :
    insertErasedCoordinate t a (eraseCoordinate t y) =
      Function.update y t a := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m =>
      exact insertNth_eraseCoordinate_eq_update t a y























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



@[simp]
theorem simplexIncidentCutTest_eraseCoordinate
    {G : Type*} {n : ℕ}
    (K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G)
    (t : Fin n) (y : Fin n → G) :
    simplexIncidentCutTest K j a t
        (eraseCoordinate t y) =
      K.edgeWeight (j.succAbove t)
        (deleteCoordinate (Fin.insertNth j a y)
          (j.succAbove t)) := by
  rw [simplexIncidentCutTest,
    insertErasedCoordinate_eraseCoordinate,
    Fin.insertNth_update]
  exact deleteCoordinate_update_same _ _ _
    |> congrArg (K.edgeWeight (j.succAbove t))

/-- A bounded simplex gives a bounded reconstructed incident cut. -/
theorem simplexIncidentCutTest_bounded
    {G : Type*} {n : ℕ}
    {K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1)) (a : G) :
    IsBoundedCutTest (simplexIncidentCutTest K j a) := by
  constructor
  · intro t z
    exact (hK (j.succAbove t) _).1
  · intro t z
    exact (hK (j.succAbove t) _).2

/-- The reconstructed cut product is exactly the incident simplex
product. -/
theorem cutTestProduct_simplexIncidentCutTest
    {G : Type*} {n : ℕ}
    (K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G)
    (y : Fin n → G) :
    cutTestProduct (simplexIncidentCutTest K j a) y =
      generalSimplexIncidentProduct K j a y := by
  unfold cutTestProduct generalSimplexIncidentProduct
  apply Fintype.prod_congr
  intro t
  exact simplexIncidentCutTest_eraseCoordinate
    K j a t y







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

open Wikipedia.SzemeredisTheorem in
/-- Edgewise face-cut discrepancy controls the term in which the
distinguished edge is changed while every incident factor comes from the
bounded system. -/
theorem solution
    {G : Type*} [Fintype G] [Nonempty G]
    {n : ℕ}
    {H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    {ε : ℝ}
    (hcut : EdgeFaceCutDiscrepancyLe H K ε)
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1)) :
    |mean (fun y =>
        (generalSimplexDistinguishedWeight H j y -
          generalSimplexDistinguishedWeight K j y) *
        generalSimplexProjectedWeight K j y)| ≤ ε := by
  have hrewrite :
      mean (fun y =>
          (generalSimplexDistinguishedWeight H j y -
            generalSimplexDistinguishedWeight K j y) *
          generalSimplexProjectedWeight K j y) =
        mean (fun a : G =>
          faceCutDifferenceCorrelation
            (canonicalEdgeFunction H j)
            (canonicalEdgeFunction K j)
            (simplexIncidentCutTest K j a)) := by
    unfold generalSimplexProjectedWeight
    calc
      mean (fun y =>
          (generalSimplexDistinguishedWeight H j y -
            generalSimplexDistinguishedWeight K j y) *
            mean (fun a =>
              generalSimplexIncidentProduct K j a y)) =
          mean (fun y =>
            mean (fun a =>
              (generalSimplexDistinguishedWeight H j y -
                generalSimplexDistinguishedWeight K j y) *
              generalSimplexIncidentProduct K j a y)) := by
        apply congrArg mean
        funext y
        exact
          (mean_smul
            (generalSimplexDistinguishedWeight H j y -
              generalSimplexDistinguishedWeight K j y)
            (fun a =>
              generalSimplexIncidentProduct K j a y)).symm
      _ = mean₂ (fun y => fun a =>
            (generalSimplexDistinguishedWeight H j y -
              generalSimplexDistinguishedWeight K j y) *
            generalSimplexIncidentProduct K j a y) := by
        rfl
      _ = mean₂ (fun a => fun y =>
            (generalSimplexDistinguishedWeight H j y -
              generalSimplexDistinguishedWeight K j y) *
            generalSimplexIncidentProduct K j a y) :=
        mean₂_comm _
      _ = mean (fun a : G =>
          faceCutDifferenceCorrelation
            (canonicalEdgeFunction H j)
            (canonicalEdgeFunction K j)
            (simplexIncidentCutTest K j a)) := by
        unfold mean₂
        apply congrArg mean
        funext a
        unfold faceCutDifferenceCorrelation
        apply congrArg mean
        funext y
        rw [cutTestProduct_simplexIncidentCutTest]
        rfl
  rw [hrewrite]
  calc
    |mean (fun a : G =>
        faceCutDifferenceCorrelation
          (canonicalEdgeFunction H j)
          (canonicalEdgeFunction K j)
          (simplexIncidentCutTest K j a))| ≤
        mean (fun a : G =>
          |faceCutDifferenceCorrelation
            (canonicalEdgeFunction H j)
            (canonicalEdgeFunction K j)
            (simplexIncidentCutTest K j a)|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _a : G => ε) := by
      apply mean_mono
      intro a
      exact hcut j
        (simplexIncidentCutTest K j a)
        (simplexIncidentCutTest_bounded hK j a)
    _ = ε := mean_const _
