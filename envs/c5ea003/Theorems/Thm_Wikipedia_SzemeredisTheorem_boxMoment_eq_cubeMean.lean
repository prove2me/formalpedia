-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_boxMoment_eq_cubeMean
-- name    : Wikipedia.SzemeredisTheorem.boxMoment_eq_cubeMean
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:46:35.536085+00:00
-- url     : https://prove2.me/theorems/f8b3cbbe-46e2-4a90-bc64-fced8aaf297a
-- title:
--   Recursive box moments equal explicit cube means
-- statement:
--   For every finite type $G$, natural $n$, and real function on $G^n$, its recursively defined box moment equals its explicit Boolean-cube mean.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/BoxNorm.lean#L186-L207

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

theorem Wikipedia.SzemeredisTheorem.boxMoment_eq_cubeMean
    {G : Type*} [Fintype G] :
    ∀ (n : ℕ) (F : (Fin n → G) → ℝ),
      boxMoment n F = cubeMean n F := by sorry
