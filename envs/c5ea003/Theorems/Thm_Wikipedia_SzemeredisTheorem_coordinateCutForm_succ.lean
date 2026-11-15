-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_coordinateCutForm_succ
-- name    : Wikipedia.SzemeredisTheorem.coordinateCutForm_succ
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:51:58.412192+00:00
-- url     : https://prove2.me/theorems/4464534b-b25f-4120-b1fb-8055b3f880cb
-- title:
--   Separating the head test factor in a coordinate cut form
-- statement:
--   For a finite type $G$, a real function $F$ of $n+1$ coordinates, and any real cut-test family $u$, the coordinate cut form equals the normalized mean over a tail tuple $y$ and head coordinate $a$ of the head factor $u_0(y)$ times the defined tail cut integrand. This is an exact identity with no boundedness or nonemptiness hypotheses.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/BoxNorm.lean#L285-L316

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

theorem Wikipedia.SzemeredisTheorem.coordinateCutForm_succ
    {G : Type*} [Fintype G] {n : ℕ}
    (F : (Fin (n + 1) → G) → ℝ)
    (u : CutTestFamily G (n + 1)) :
    coordinateCutForm (n + 1) F u =
      mean₂ fun y : Fin n → G => fun a : G =>
        u 0 y * tailCutIntegrand F u y a := by sorry
