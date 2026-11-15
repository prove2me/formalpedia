-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cyclicAPVal_secondDifference_eq_zero
-- name    : Wikipedia.SzemeredisTheorem.cyclicAPVal_secondDifference_eq_zero
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:53:09.746991+00:00
-- url     : https://prove2.me/theorems/053cee79-4e79-4891-bb37-b449af54f765
-- title:
--   Short-interval cyclic representatives have zero integer second differences
-- statement:
--   Let $N>0$ and suppose the standard representatives $v_i$ of the first $k$ terms of a cyclic progression all lie in an integer interval $[L,U]$ with $2(U-L)<N$. For every $j$ with $j+2<k$,
--
--   $$
--   v_{j+2}-2v_{j+1}+v_j=0
--   $$
--
--   as an integer equality. The cyclic difference may be zero.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/ShortInterval.lean#L36-L64

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.ModEq
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
open Wikipedia.SzemeredisTheorem

theorem Wikipedia.SzemeredisTheorem.cyclicAPVal_secondDifference_eq_zero {k N : ℕ} [NeZero N]
    (a d : ZMod N) (L U : ℤ)
    (hmem :
      ∀ i : ℕ, i < k →
        L ≤ cyclicAPVal a d i ∧ cyclicAPVal a d i ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (j : ℕ) (hj : j + 2 < k) :
    (cyclicAPVal a d (j + 2) : ℤ) -
        2 * cyclicAPVal a d (j + 1) +
        cyclicAPVal a d j = 0 := by sorry
