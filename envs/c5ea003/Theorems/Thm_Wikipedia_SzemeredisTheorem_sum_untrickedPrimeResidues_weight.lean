-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_untrickedPrimeResidues_weight
-- name    : Wikipedia.SzemeredisTheorem.sum_untrickedPrimeResidues_weight
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:30:24.836133+00:00
-- url     : https://prove2.me/theorems/4d394c4b-b093-49d3-bcac-d5bd0de7389c
-- title:
--   The logarithmic mass of an embedded prime residue class
-- statement:
--   Let $N\ne0$, $W>0$, and $b\in\mathbb N$, and let $\alpha\in\mathbb R$. The sum of the W-tricked prime weight over the untricked prime residues equals $\alpha\varphi(W)/W$ times the sum of $\log p$ over the selected quarter-interval residue class.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/WTrickDensity.lean#L176-L195

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

theorem Wikipedia.SzemeredisTheorem.sum_untrickedPrimeResidues_weight
    {W N b : ℕ} [NeZero N] (α : ℝ) (hW : 0 < W) :
    ∑ n ∈ untrickedPrimeResidues N W b,
        wTrickedPrimeWeight α W b n =
      α * ((W.totient : ℝ) / W) *
        ∑ p ∈ quarterIntervalResidueClass W N b, log p := by sorry
