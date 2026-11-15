-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
-- name    : GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:59:46.178992+00:00
-- url     : https://prove2.me/theorems/58657d02-2fdd-4c94-b0c8-0d6aeeed4829
-- title:
--   Replacing a Boolean selector on a single CFZ face
-- statement:
--   Fix a face colour $j$, a Boolean selector on that face's deleted cube, and an existing Boolean selector on the whole CFZ family. The overwrite operation uses the new selector on face $j$ and the existing selector on every other face. Equality transport identifies the deleted-cube index types at the distinguished face. This makes it possible to vary one face's subproduct while retaining all other selected forms.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/WeightedStrongLinearForms.lean#L23-L31

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
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
# Weighted endpoint of the strong linear-forms argument

The CFZ densification proof applies Cauchy--Schwarz repeatedly to a
centered factor on one simplex face.  At the final doubled stage, every
remaining relatively bounded factor has been replaced by either its
majorant or by one.  The resulting expression is

* the product of all centered copies of the selected face; times
* an arbitrary Boolean-selected subproduct of the other CFZ forms.

This file proves the exact quantitative linear-forms estimate for that
endpoint.  The still-missing recursive Cauchy--Schwarz bridge belongs in
the same module after this algebraic target.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Replace the selector on one CFZ face while retaining every selector on
the other faces. -/
def overwriteFaceExponent
    {k : ℕ} (j : Fin k)
    (face : BooleanCube (DeletedCube k j))
    (other : LinearFormsExponent k) :
    LinearFormsExponent k :=
  fun i ω =>
    if h : i = j then face (h ▸ ω) else other i ω













end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.overwriteFaceExponent.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


