-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:01:20.815204+00:00
-- url     : https://prove2.me/theorems/53aed555-b593-4682-8655-7f284c8ee621
-- title:
--   Heterogeneous AP-simplex weights and conditional projections
-- statement:
--   A heterogeneous AP-face family assigns a real function on $\mathbb Z/N\mathbb Z$ to each of $n+1$ face colours. Its simplex edge weight at colour $i$ is that function evaluated on the canonical AP-simplex form.
--
--   For a missing colour $j$, the incident product multiplies all other face weights after inserting a value into coordinate $j$. When $N>0$, its conditional projection averages over that inserted coordinate, leaving a function on the deleted face. The untouched-face bound requires $0\le g_i\le\nu_i$ precisely for colours $i\ne j$; it imposes no bound on the removed colour.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeSimplexIteration.lean#L27-L109

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
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

/-- One real weight on `ZMod N` for every colour of the canonical
`(n + 1)`-colour AP simplex. -/
abbrev APFaceWeightFamily (n N : ℕ) :=
  (i : Fin (n + 1)) → ZMod N → ℝ

/-- The AP-simplex system associated to a heterogeneous family of face
weights. -/
def apHeterogeneousSimplexSystem
    (n N : ℕ) (g : APFaceWeightFamily n N) :
    WeightedSimplexSystem
      (fun _ : Fin (n + 1) => ZMod N) where
  edgeWeight i x :=
    g i (apSimplexForm (n + 1) N i x)



/-- Product of all heterogeneous AP face weights except colour `j`, after
inserting the missing `j` coordinate. -/
def apHeterogeneousIncidentProduct
    (n N : ℕ) (g : APFaceWeightFamily n N)
    (j : Fin (n + 1))
    (a : ZMod N) (y : Fin n → ZMod N) : ℝ :=
  ∏ t : Fin n,
    g (j.succAbove t)
      (apSimplexForm (n + 1) N (j.succAbove t)
        (deleteCoordinate (Fin.insertNth j a y)
          (j.succAbove t)))

/-- Conditional projection of the heterogeneous non-`j` product onto the
deleted `j` face. -/
noncomputable def apHeterogeneousProjectedWeight
    (n N : ℕ) [NeZero N]
    (g : APFaceWeightFamily n N)
    (j : Fin (n + 1)) :
    (Fin n → ZMod N) → ℝ :=
  fun y =>
    mean (fun a =>
      apHeterogeneousIncidentProduct n N g j a y)







/-- A concise predicate for the bounds on precisely the colours untouched
by projection at `j`. -/
def APUntouchedFaceBounds
    {n N : ℕ}
    (g ν : APFaceWeightFamily n N)
    (j : Fin (n + 1)) : Prop :=
  ∀ t z,
    0 ≤ g (j.succAbove t) z ∧
      g (j.succAbove t) z ≤ ν (j.succAbove t) z







/-! ## Projection bounds -/













/-! ## Exact heterogeneous count and pairing -/













/-! ## A concrete full-to-projected state transition -/































namespace RelativeDensificationIteration



end RelativeDensificationIteration











end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.apHeterogeneousProjectedWeight.congr_simp
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


