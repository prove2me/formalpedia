-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_coordinateCutForm_pow_le_boxMoment
-- name    : Wikipedia.SzemeredisTheorem.coordinateCutForm_pow_le_boxMoment
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:51:57.995203+00:00
-- url     : https://prove2.me/theorems/ed826a03-19f4-4f65-8cc6-8513b7bd2f67
-- title:
--   The coordinate cut form is bounded by its box moment
-- statement:
--   Let $G$ be nonempty and finite. For every natural $n$, real tuple function $F:G^n\to\mathbb R$, and deleted-coordinate test family $u$ with $|u_i|\le1$,
--
--   $$
--   Q_n(F,u)^{2^n}\le B_n(F),
--   $$
--
--   where $Q_n$ is the coordinate cut form and $B_n$ the recursive box moment. The exponent at $n=0$ is one, as in the signed formal statement.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/BoxNorm.lean#L377-L419

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Finite box moments and generalized von Neumann

This file packages the iterated Cauchy--Schwarz argument for a function on a
finite product.  A coordinate cut form pairs the function with one bounded
factor for every deleted coordinate.  Its `2 ^ n`-th power is bounded by the
recursive `n`-dimensional box moment.

The recursive definition duplicates one coordinate at a time.  It is
definitionally aligned with the Cauchy--Schwarz proof and is equivalent to
the usual average of the product over all vertices of an `n`-cube.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.coordinateCutForm_pow_le_boxMoment
    {G : Type*} [Fintype G] [Nonempty G] :
    ∀ (n : ℕ) (F : (Fin n → G) → ℝ)
      (u : CutTestFamily G n),
      IsAbsBoundedCutTest u →
        coordinateCutForm n F u ^ (2 ^ n) ≤
          boxMoment n F := by sorry
