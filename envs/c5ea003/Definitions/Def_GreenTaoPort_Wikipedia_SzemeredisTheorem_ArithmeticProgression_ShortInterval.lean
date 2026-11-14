-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:37.730344+00:00
-- url     : https://prove2.me/theorems/fb124d18-ed2b-41b7-a7fb-54b7e1a186ea
-- title:
--   Natural representatives of cyclic progression terms
-- statement:
--   For a positive natural modulus $N$, residues $a,d\in\mathbb Z/N\mathbb Z$, and a natural position $j$, define
--
--   $$
--   v_j=\operatorname{val}(a+jd)\in\{0,\ldots,N-1\},
--   $$
--
--   using the standard natural representative. The definition allows every natural position rather than restricting $j$ to a fixed finite length. It supplies the sequence used later to unwrap a cyclic progression whose representatives lie in a sufficiently short interval.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/ShortInterval.lean#L15-L18

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Mathlib.Data.Int.ModEq
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Unwrapping cyclic progressions in a short interval

A progression obtained by transference lives in `ZMod N`.  The prime weight
is supported on an interval much shorter than a full residue system.  In
that situation the standard representatives have second difference zero
over the integers, so they form an ordinary integer progression.
-/

namespace Wikipedia.SzemeredisTheorem

/-- The standard natural representative of the `j`th term of a cyclic
progression. -/
def cyclicAPVal {N : ℕ} [NeZero N] (a d : ZMod N) (j : ℕ) : ℕ :=
  (a + (j : ZMod N) * d).val















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cyclicAPVal.congr_simp,
    `Wikipedia.SzemeredisTheorem.cyclicAPVal.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


