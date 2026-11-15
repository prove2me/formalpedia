-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_containsAP_of_cyclicAPVal_shortInterval
-- name    : Wikipedia.SzemeredisTheorem.containsAP_of_cyclicAPVal_shortInterval
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:51:57.39546+00:00
-- url     : https://prove2.me/theorems/6e6db7d8-06aa-437f-b70a-41b8ed41888c
-- title:
--   A short nonconstant cyclic progression yields an ordinary natural progression
-- statement:
--   Let $N>0$, $k\ge2$, and $a,d\in\mathbb Z/N\mathbb Z$ with $d\ne0$. Suppose the standard representatives of the first $k$ terms lie in a set $A\subseteq\mathbb N$ and in an integer interval $[L,U]$ satisfying $2(U-L)<N$.
--
--   Then $A$ contains an ordinary $k$-term arithmetic progression with a positive natural common difference. The conclusion is an existence statement, allowing reversal of the order if the short representative progression decreases.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/ArithmeticProgression/ShortIntervalLift.lean#L15-L67

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Lifting a short cyclic progression to the natural numbers

After unwrapping a cyclic progression, its integer common difference can
have either orientation.  A positive difference already gives the required
natural-number progression.  A negative difference gives the same
progression after reversing its `k` terms.
-/
open Wikipedia.SzemeredisTheorem

theorem Wikipedia.SzemeredisTheorem.containsAP_of_cyclicAPVal_shortInterval
    {A : Set ℕ} {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (hk : 2 ≤ k)
    (L U : ℤ)
    (hinterval :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (hA : ∀ j : ℕ, j < k → cyclicAPVal a d j ∈ A) :
    ContainsAP A k := by sorry
