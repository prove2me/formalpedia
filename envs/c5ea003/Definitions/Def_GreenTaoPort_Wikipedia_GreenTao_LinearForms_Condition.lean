-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
-- name    : GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:40.164752+00:00
-- url     : https://prove2.me/theorems/bbd825ac-0962-4788-a8c9-c19febf59b59
-- title:
--   The empty exponent pattern in a linear-forms system
-- statement:
--   For a natural progression length $k$, the empty exponent pattern assigns the Boolean value false to every index in the associated Conlon–Fox–Zhao system. It therefore selects no factors in the Boolean expansion of a linear-forms product. This definition supplies the empty-pattern normalization test; it is defined for every natural $k$, including the empty index cases.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/LinearForms/Condition.lean#L13-L15

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Elementary properties of the linear-forms condition

This file records the normalization and positivity facts that every later
transference estimate uses.  The deep input—that the W-tricked Selberg
majorant satisfies this condition—is isolated in the sieve layer.
-/

namespace Wikipedia.SzemeredisTheorem

/-- Select no factors from the CFZ system. -/
def emptyLinearFormsExponent (k : ℕ) : LinearFormsExponent k :=
  fun _ _ => false













end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.emptyLinearFormsExponent.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


