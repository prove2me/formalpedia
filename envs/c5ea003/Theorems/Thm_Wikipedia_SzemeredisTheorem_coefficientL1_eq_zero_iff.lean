-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_coefficientL1_eq_zero_iff
-- name    : Wikipedia.SzemeredisTheorem.coefficientL1_eq_zero_iff
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:49:45.35383+00:00
-- url     : https://prove2.me/theorems/342e0a8e-6927-450d-ac77-d4f9d69a1f76
-- title:
--   The coefficient ℓ¹ norm vanishes exactly at the zero vector
-- statement:
--   For a real coefficient vector $c$ indexed by a finite type,
--
--   $$
--   \sum_t|c_t|=0\quad\Longleftrightarrow\quad c=0.
--   $$
--
--   The equality on the right is pointwise equality with the zero function.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/DenseModel.lean#L411-L426

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

theorem Wikipedia.SzemeredisTheorem.coefficientL1_eq_zero_iff
    {τ : Type*} [Fintype τ] (c : τ → ℝ) :
    coefficientL1 c = 0 ↔ c = 0 := by sorry
