-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_dual_apply_dualErrorVector
-- name    : Wikipedia.SzemeredisTheorem.dual_apply_dualErrorVector
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:53:09.749856+00:00
-- url     : https://prove2.me/theorems/db5fcc3f-0e47-479a-8599-37f6ff24632f
-- title:
--   A dual functional on its signed error vector gives the coefficient ℓ¹ norm
-- statement:
--   Let $L$ be a continuous real linear functional on a finite coordinate space, let $c_t=L(e_t)$ be its standard-basis coefficients, and let $\varepsilon\in\mathbb R$. For the error vector $v_t=\varepsilon\operatorname{sign}(c_t)$,
--
--   $$
--   L(v)=\varepsilon\sum_t|c_t|.
--   $$
--
--   The scalar $\varepsilon$ is arbitrary.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/DenseModel.lean#L540-L556

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Finite dense-model duality primitives

The dense-model argument takes place in the finite-dimensional space of
real functions on a finite set.  This file isolates its elementary dual
calculus: normalized pairings, the unit cube, positive parts, and the exact
support function of the unit cube.  In particular, a hyperplane separating
a nonnegative `f ≤ ν` from all `[0,1]`-valued models produces a positive
correlation of `ν - 1` with the positive part of the separator.
-/
open Wikipedia.SzemeredisTheorem
open scoped Pointwise

theorem Wikipedia.SzemeredisTheorem.dual_apply_dualErrorVector
    {τ : Type*} [Fintype τ]
    (ε : ℝ) (L : StrongDual ℝ (τ → ℝ)) :
    L (dualErrorVector ε L) =
      ε * coefficientL1 (dualCoefficient L) := by sorry
