-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.generalSimplexCount_eq_projectedPairing
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:53:13.203462+00:00
-- url     : https://prove2.me/submissions/60c0f1ca-b772-4b42-a767-ec8687c3b1d1

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_GeneralRelativeSimplexStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_insertNth

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







/-- Deleting coordinate `j` from a full tuple agrees with the canonical
`Fin n` presentation of the remaining coordinates. -/
theorem deleteCoordinate_eq_finTupleToDeletedVector
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1)) (x : Fin (n + 1) → G) :
    deleteCoordinate x j =
      finTupleToDeletedVector j
        (fun t => x (j.succAbove t)) := by
  funext i
  change x i.1 =
    x (j.succAbove ((finSuccAboveEquiv j).symm i))
  apply congrArg x
  have hi :=
    congrArg Subtype.val
      ((finSuccAboveEquiv j).apply_symm_apply i)
  exact hi.symm







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











/-- Inserting the missing coordinate factors the simplex weight into the
incident product and the distinguished edge. -/
theorem generalSimplexWeight_insertNth
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (a : G) (y : Fin n → G) :
    H.simplexWeight (Fin.insertNth j a y) =
      generalSimplexIncidentProduct H j a y *
        generalSimplexDistinguishedWeight H j y := by
  rw [WeightedSimplexSystem.simplexWeight,
    Fin.prod_univ_succAbove _ j]
  have hdistinguished :
      H.edgeWeight j
          (deleteCoordinate (Fin.insertNth j a y) j) =
        generalSimplexDistinguishedWeight H j y := by
    simp [generalSimplexDistinguishedWeight,
      deleteCoordinate_eq_finTupleToDeletedVector]
  rw [hdistinguished, mul_comm]
  rfl



/-! ## Pointwise bounds and projected domination -/















/-! ## The generic analytic transition -/



/-! ## The constant-one majorant -/















/-! ## Generic full and projected states -/

























/-! ## Consuming the recursive selectable endpoint -/















end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Projection of an arbitrary weighted simplex -/

open Wikipedia.SzemeredisTheorem in
/-- Exact arbitrary-simplex projection identity. -/
theorem solution
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    H.simplexCount =
      mean (fun y =>
        generalSimplexProjectedWeight H j y *
          generalSimplexDistinguishedWeight H j y) := by
  rw [WeightedSimplexSystem.simplexCount,
    mean_insertNth n j, mean₂_comm]
  unfold mean₂
  apply congrArg mean
  funext y
  calc
    mean (fun a : G =>
        H.simplexWeight (Fin.insertNth j a y)) =
        mean (fun a : G =>
          generalSimplexIncidentProduct H j a y *
            generalSimplexDistinguishedWeight H j y) := by
      apply congrArg mean
      funext a
      exact generalSimplexWeight_insertNth H j a y
    _ = mean (fun a : G =>
          generalSimplexDistinguishedWeight H j y *
            generalSimplexIncidentProduct H j a y) := by
      apply congrArg mean
      funext a
      ring
    _ = generalSimplexDistinguishedWeight H j y *
        mean (fun a : G =>
          generalSimplexIncidentProduct H j a y) :=
      mean_smul _ _
    _ = generalSimplexProjectedWeight H j y *
        generalSimplexDistinguishedWeight H j y := by
      rw [mul_comm]
      rfl
