-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:02:29.667197+00:00
-- url     : https://prove2.me/theorems/acc70a0f-1f8e-4dd0-893d-e76c15baefd8
-- title:
--   Activity-masked majorants for recursive AP-simplex densification
-- statement:
--   An activity mask assigns to each face colour either the sparse majorant $\nu$ or the constant function one. The masked incident product multiplies the non-distinguished face majorants, and its conditional projection averages over the missing coordinate at a positive cyclic modulus.
--
--   Two Boolean linear-forms selectors record the projected moments: the one-copy selector takes the false projection vertex at every active incident colour; the two-copy selector takes both projection vertices there. Both omit the distinguished colour and every inactive colour. Thus the same explicit indexing describes each intermediate mixture of sparse and already densified faces.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RecursiveRelativeSimplex.lean#L26-L114

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
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
# Mixed projected moments for recursive relative densification

After one colour has been densified, its majorant is the constant function
one.  At the next stage the projected majorant is therefore not the product
of a common `ν` on every incident colour: it is a mixed product, with `ν`
only on the colours which remain sparse and `1` on the colours already
densified.

This file closes that moment gap.  A Boolean mask records the remaining
sparse colours.  We expand the first and second moments of the corresponding
projected majorant as explicit subproducts of the original CFZ linear-forms
system.  Consequently one unchanged `HasLinearFormsCondition` supplies the
moment package for every recursive mask, and hence supplies the next
heterogeneous full-to-projected state transition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Majorants with previously densified colours set to one -/

/-- The heterogeneous face-majorant family which uses `ν` on active
colours and the constant function one on colours already densified. -/
def apMaskedFaceMajorant
    {k N : ℕ}
    (ν : ZMod N → ℝ) (active : Fin k → Bool) :
    (i : Fin k) → ZMod N → ℝ :=
  fun i z => if active i then ν z else 1





/-- Product of the still-active incident majorants after inserting the
eliminated coordinate.  Inactive colours contribute literal factors `1`. -/
def apMaskedIncidentMajorantProduct
    (n N : ℕ) (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1))
    (a : ZMod N) (y : Fin n → ZMod N) : ℝ :=
  apHeterogeneousIncidentProduct n N
    (apMaskedFaceMajorant ν active) j a y

/-- Conditional projection of the mixed incident majorant product. -/
noncomputable def apMaskedProjectedMajorant
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    (Fin n → ZMod N) → ℝ :=
  apHeterogeneousProjectedWeight n N
    (apMaskedFaceMajorant ν active) j



/-! ## Masked CFZ selectors -/

/-- Select one projected copy on every active incident colour and no form
on an inactive colour. -/
noncomputable def apMaskedProjectedOneCopyExponent
    (n : ℕ) (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    LinearFormsExponent (n + 1) :=
  fun i ω =>
    if i = j then false
    else if active i then
      if ω = apProjectionVertex j i false then true else false
    else false

/-- Select two projected copies on every active incident colour and no form
on an inactive colour. -/
noncomputable def apMaskedProjectedTwoCopyExponent
    (n : ℕ) (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    LinearFormsExponent (n + 1) :=
  fun i ω =>
    if i = j then false
    else if active i then
      if
        ω = apProjectionVertex j i false ∨
          ω = apProjectionVertex j i true
      then true
      else false
    else false





/-! ## Exact mixed projected moments -/





/-! ## The recursive moment and state-transition certificates -/





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.apMaskedFaceMajorant.eq_1,
    `Wikipedia.SzemeredisTheorem.apMaskedProjectedOneCopyExponent.eq_1,
    `Wikipedia.SzemeredisTheorem.apMaskedProjectedTwoCopyExponent.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


