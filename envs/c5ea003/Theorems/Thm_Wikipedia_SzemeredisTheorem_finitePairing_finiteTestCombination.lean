-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_finitePairing_finiteTestCombination
-- name    : Wikipedia.SzemeredisTheorem.finitePairing_finiteTestCombination
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:04:52.170279+00:00
-- url     : https://prove2.me/theorems/6e20e335-2e52-4efa-8d73-7922efd2ecdb
-- title:
--   Pairing distributes over a finite test combination
-- statement:
--   For finite types $\Omega,\tau$, a real function $f$ on $\Omega$, real tests $q_t$, and real coefficients $c_t$, the normalized finite pairing satisfies $\langle f,\sum_t c_tq_t\rangle=\sum_t c_t\langle f,q_t\rangle$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/DenseModel.lean#L479-L501

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

theorem Wikipedia.SzemeredisTheorem.finitePairing_finiteTestCombination
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (f : Ω → ℝ) (q : τ → Ω → ℝ) (c : τ → ℝ) :
    finitePairing f (finiteTestCombination q c) =
      ∑ t, c t * finitePairing f (q t) := by sorry
