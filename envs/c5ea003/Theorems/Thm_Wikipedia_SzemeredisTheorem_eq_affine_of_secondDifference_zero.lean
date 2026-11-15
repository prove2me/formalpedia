-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_eq_affine_of_secondDifference_zero
-- name    : Wikipedia.SzemeredisTheorem.eq_affine_of_secondDifference_zero
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:53:53.28241+00:00
-- url     : https://prove2.me/theorems/4f645f08-2a06-440f-a9dd-8b7a8ff70626
-- title:
--   Zero second differences make a finite integer sequence segment affine
-- statement:
--   Let $z:\mathbb N\to\mathbb Z$ and $k\in\mathbb N$. If $z_{j+2}-2z_{j+1}+z_j=0$ whenever $j+2<k$, then for every $j<k$,
--
--   $$
--   z_j=z_0+j(z_1-z_0).
--   $$
--
--   No lower bound on $k$ is needed.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/ArithmeticProgression/ShortInterval.lean#L66-L89

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

theorem Wikipedia.SzemeredisTheorem.eq_affine_of_secondDifference_zero
    (z : ℕ → ℤ) (k : ℕ)
    (hsecond :
      ∀ j : ℕ, j + 2 < k →
        z (j + 2) - 2 * z (j + 1) + z j = 0) :
    ∀ j : ℕ, j < k →
      z j = z 0 + (j : ℤ) * (z 1 - z 0) := by sorry
