-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_card_class_mean_lower_bound
-- name    : Wikipedia.SzemeredisTheorem.card_class_mean_lower_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:48:40.877271+00:00
-- url     : https://prove2.me/theorems/0e4fb6bf-e453-4f3f-992b-823c12782a7b
-- title:
--   A residue-class prime count gives a mean prime-weight lower bound
-- statement:
--   Let $N>0$, $W>0$, $b\in\mathbb N$, and $\alpha\ge0$. Put $X=W\lfloor N/8\rfloor$ and let $P$ consist of primes in $(\lfloor X/4\rfloor,X]$ with remainder $b$ modulo $W$. Then the $W$-tricked prime weight on $\mathbb Z/N\mathbb Z$ has mean at least
--
--   $$
--   \frac{\alpha\varphi(W)}{WN}\,|P|\log(\lfloor X/4\rfloor+1).
--   $$
--
--   No restriction on the natural residue parameter $b$ is added.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/WTrickDensity.lean#L239-L258

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

theorem Wikipedia.SzemeredisTheorem.card_class_mean_lower_bound
    {W N b : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α) (hW : 0 < W) :
    (α * ((W.totient : ℝ) / W) *
        ((#(quarterIntervalResidueClass W N b) : ℝ) *
          log (wTrickPrimeScale W N / 4 + 1 : ℕ))) / N ≤
      mean (wTrickedPrimeWeight α W b : ZMod N → ℝ) := by sorry
