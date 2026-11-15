-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_dual_apply_eq_sum_coefficient
-- name    : Wikipedia.SzemeredisTheorem.dual_apply_eq_sum_coefficient
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:53:10.767279+00:00
-- url     : https://prove2.me/theorems/20e3f16c-811a-4e92-8e12-81119869bc4c
-- title:
--   A finite-dimensional dual functional is the sum against its coefficients
-- statement:
--   For a continuous real linear functional $L$ on a finite coordinate space and any vector $v$,
--
--   $$
--   L(v)=\sum_t L(e_t)v_t,
--   $$
--
--   where $e_t$ is the standard vector supported at coordinate $t$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/DenseModel.lean#L379-L399

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

theorem Wikipedia.SzemeredisTheorem.dual_apply_eq_sum_coefficient
    {τ : Type*} [Fintype τ]
    (L : StrongDual ℝ (τ → ℝ)) (v : τ → ℝ) :
    L v = ∑ t, dualCoefficient L t * v t := by sorry
