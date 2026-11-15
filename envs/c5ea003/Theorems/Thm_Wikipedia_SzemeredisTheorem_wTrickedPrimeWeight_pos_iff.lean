-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_wTrickedPrimeWeight_pos_iff
-- name    : Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_pos_iff
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:34.301459+00:00
-- url     : https://prove2.me/theorems/cfc3eea4-7868-4d26-85f3-13ea626c197e
-- title:
--   Support of the W-tricked prime weight
-- statement:
--   Let $N,W\ge1$ be natural numbers, let $b$ be a natural number, and let $\alpha>0$ be real. For $n\in\mathbb Z/N\mathbb Z$, denote its standard representative by $\widetilde n$, its W-tricked value by $v_{W,b}(n)$, and the Green–Tao interval by $I_N$. Then
--   $$
--   f_{\alpha,W,b}(n)>0\quad\Longleftrightarrow\quad \widetilde n\in I_N\ \text{ and }\ \operatorname{Prime}(v_{W,b}(n)).
--   $$
--   Here $f_{\alpha,W,b}$ is the W-tricked prime weight defined in the imported sieve data.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/WTrick.lean#L73-L96

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# W-tricked prime weight and Selberg majorant

This file defines the two functions compared in the final transference
argument.  Both are localized to a short interval of standard
representatives.  Outside that interval the prime weight is zero and the
majorant is one; inside it, the majorant is the normalized Selberg square at
`W * n + b`.
-/
open Wikipedia.SzemeredisTheorem

theorem Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_pos_iff {N : ℕ} [NeZero N]
    {α : ℝ} (hα : 0 < α) {W : ℕ} (hW : 0 < W)
    (b : ℕ) (n : ZMod N) :
    0 < wTrickedPrimeWeight α W b n ↔
      n.val ∈ greenTaoInterval N ∧
        Nat.Prime (wTrickedValue W b n) := by sorry
