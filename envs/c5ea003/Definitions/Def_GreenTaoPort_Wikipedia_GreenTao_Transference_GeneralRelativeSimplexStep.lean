-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_GeneralRelativeSimplexStep
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_GeneralRelativeSimplexStep
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:03:33.987653+00:00
-- url     : https://prove2.me/theorems/ea267360-c7d0-484b-bdd7-08dbbb69fb85
-- title:
--   Incident products and conditional projections for arbitrary simplex weights
-- statement:
--   For a weighted simplex with $n+1$ colours and a distinguished colour $j$, the incident product multiplies all weights other than $j$ after inserting a value into the missing coordinate. When the vertex type is finite, averaging over that inserted value gives a real function on the deleted $j$ face.
--
--   The distinguished edge is separately expressed in canonical $n$-coordinate face coordinates. The untouched-edge predicate bounds precisely the other colours between zero and their corresponding majorant weights. A constant-one simplex system is also supplied. These constructions apply to arbitrary simplex edge functions, without assuming that each edge is an AP-form pullback.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/GeneralRelativeSimplexStep.lean#L25-L260

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
import Lean
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


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

/-- Product of all edge weights except colour `j`, after inserting the
missing `j` coordinate. -/
def generalSimplexIncidentProduct
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (a : G) (y : Fin n → G) : ℝ :=
  ∏ t : Fin n,
    H.edgeWeight (j.succAbove t)
      (deleteCoordinate (Fin.insertNth j a y)
        (j.succAbove t))

/-- Conditional projection of all non-distinguished edge weights. -/
noncomputable def generalSimplexProjectedWeight
    {G : Type*} [Fintype G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    (Fin n → G) → ℝ :=
  fun y => mean fun a =>
    generalSimplexIncidentProduct H j a y



/-- Distinguished edge in canonical `Fin n` deleted-face coordinates. -/
noncomputable def generalSimplexDistinguishedWeight
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    (Fin n → G) → ℝ :=
  fun y => H.edgeWeight j (finTupleToDeletedVector j y)







/-! ## Pointwise bounds and projected domination -/

/-- Bounds on precisely the edges untouched when projecting at `j`. -/
def GeneralSimplexUntouchedBounds
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) : Prop :=
  ∀ t x,
    0 ≤ H.edgeWeight (j.succAbove t) x ∧
      H.edgeWeight (j.succAbove t) x ≤
        K.edgeWeight (j.succAbove t) x













/-! ## The generic analytic transition -/



/-! ## The constant-one majorant -/

/-- The constant-one weighted simplex. -/
def oneWeightedSimplexSystem
    (G : Type*) (n : ℕ) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G) where
  edgeWeight _ _ := 1













/-! ## Generic full and projected states -/

























/-! ## Consuming the recursive selectable endpoint -/















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.generalSimplexDistinguishedWeight.eq_1,
    `Wikipedia.SzemeredisTheorem.generalSimplexIncidentProduct.eq_1,
    `Wikipedia.SzemeredisTheorem.generalSimplexProjectedWeight.eq_1,
    `Wikipedia.SzemeredisTheorem.oneWeightedSimplexSystem.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


