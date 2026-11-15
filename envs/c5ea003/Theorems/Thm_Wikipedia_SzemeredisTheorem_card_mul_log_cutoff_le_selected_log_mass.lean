-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_card_mul_log_cutoff_le_selected_log_mass
-- name    : Wikipedia.SzemeredisTheorem.card_mul_log_cutoff_le_selected_log_mass
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:48:36.543469+00:00
-- url     : https://prove2.me/theorems/8acf66d7-c21f-42f0-9319-c2eb9a46e7fe
-- title:
--   Prime logarithmic mass bounds the count times its interval cutoff
-- statement:
--   For natural $W,N,b$, put $X=W\lfloor N/8\rfloor$ and let $P$ be the primes in $(\lfloor X/4\rfloor,X]$ with remainder $b$ modulo $W$. Then
--
--   $$
--   |P|\log(\lfloor X/4\rfloor+1)\le\sum_{p\in P}\log p.
--   $$
--
--   All natural parameters are allowed, including degenerate cases where the prime set is empty.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/WTrickDensity.lean#L219-L237

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrickDensity
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# From primes in a quarter interval to a dense W-tricked prime weight

This file supplies the finite arithmetic bridge in the `W`-trick.  We take
`X = W * (N / 8)`, choose one reduced class among the primes in `(X / 4, X]`,
and send a prime `p` in that class to `(p - b) / W`.  The generous constants
in `greenTaoInterval` make this quotient lie in `[N / 64, N / 4]`.
-/
open Wikipedia.SzemeredisTheorem
open Finset Real Filter
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.card_mul_log_cutoff_le_selected_log_mass
    {W N b : ℕ} :
    (#(quarterIntervalResidueClass W N b) : ℝ) *
        log (wTrickPrimeScale W N / 4 + 1 : ℕ) ≤
      ∑ p ∈ quarterIntervalResidueClass W N b, log p := by sorry
