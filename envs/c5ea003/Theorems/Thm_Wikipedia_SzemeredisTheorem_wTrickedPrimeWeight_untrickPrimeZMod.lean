-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_wTrickedPrimeWeight_untrickPrimeZMod
-- name    : Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_untrickPrimeZMod
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:36.083305+00:00
-- url     : https://prove2.me/theorems/10093f7c-d9d0-4862-8292-466e4e9b9a0d
-- title:
--   The prime weight at an untricked selected prime
-- statement:
--   Let $N\ne0$, $W>0$, $\alpha\in\mathbb R$, and let $p$ belong to the selected quarter-interval residue class. The W-tricked prime weight at the residue obtained by untricking $p$ equals $\alpha\varphi(W)\log p/W$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/WTrickDensity.lean#L157-L174

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

@[simp]
theorem Wikipedia.SzemeredisTheorem.wTrickedPrimeWeight_untrickPrimeZMod
    {W N b p : ℕ} [NeZero N] (α : ℝ)
    (hW : 0 < W) (hp : p ∈ quarterIntervalResidueClass W N b) :
    wTrickedPrimeWeight α W b (untrickPrimeZMod N W b p) =
      α * ((W.totient : ℝ) / W) * log p := by sorry
