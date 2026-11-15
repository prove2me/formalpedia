-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_chebyshev_wTrick_lower_bound
-- name    : Wikipedia.SzemeredisTheorem.chebyshev_wTrick_lower_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:49:45.88713+00:00
-- url     : https://prove2.me/theorems/4b873f67-73cc-4a3d-96db-618df89baba4
-- title:
--   A uniform lower bound after W-trick scaling and logarithmic cutoff
-- statement:
--   Let $W>0$, $\alpha\ge0$, and $N\ge16$ be as specified, with $X=W\lfloor N/8\rfloor\ge16$. Then
--
--   $$
--   \frac{\alpha\log2}{128}
--   \le\frac{\alpha}{WN}\,
--   \frac{\log2}{4}\frac{X}{\log X}
--   \log(\lfloor X/4\rfloor+1).
--   $$
--
--   Here $W,N$ are natural, and all logarithms are real natural logarithms.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/WTrickDensity.lean#L532-L588

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

theorem Wikipedia.SzemeredisTheorem.chebyshev_wTrick_lower_bound
    {W N : ℕ} (hW : 0 < W)
    {α : ℝ} (hα : 0 ≤ α)
    (hN : 16 ≤ N)
    (hscale : 16 ≤ wTrickPrimeScale W N) :
    α * log 2 / 128 ≤
      (((α / (W : ℝ)) *
          (log 2 / 4 * (wTrickPrimeScale W N : ℝ) /
            log (wTrickPrimeScale W N)) *
          log (wTrickPrimeScale W N / 4 + 1 : ℕ)) / N) := by sorry
