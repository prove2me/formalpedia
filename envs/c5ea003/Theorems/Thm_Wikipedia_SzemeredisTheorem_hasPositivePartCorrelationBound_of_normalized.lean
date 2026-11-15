-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_hasPositivePartCorrelationBound_of_normalized
-- name    : Wikipedia.SzemeredisTheorem.hasPositivePartCorrelationBound_of_normalized
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:09:19.232309+00:00
-- url     : https://prove2.me/theorems/d6cdc56c-5968-4a20-baac-55af191cf097
-- title:
--   Normalized positive-part control implies the homogeneous bound
-- statement:
--   For finite types $\Omega,\tau$, arbitrary real test family $q$, real majorant $\nu$, and real $\varepsilon$, a one-sided positive-part correlation bound $\varepsilon$ for coefficient vectors of $\ell^1$ norm $1$ implies the homogeneous bound $\varepsilon\|c\|_1$ for every coefficient vector $c$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/DenseModel.lean#L715-L750

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

theorem Wikipedia.SzemeredisTheorem.hasPositivePartCorrelationBound_of_normalized
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ) (ε : ℝ)
    (h :
      HasNormalizedPositivePartCorrelationBound q ν ε) :
    HasPositivePartCorrelationBound q ν ε := by sorry
