-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_reducedResidue_chebyshev_mean_lower_bound
-- name    : Wikipedia.SzemeredisTheorem.exists_reducedResidue_chebyshev_mean_lower_bound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:02:43.281083+00:00
-- url     : https://prove2.me/theorems/150b5684-0dc0-4c9d-b731-3708358648fa
-- title:
--   A Chebyshev estimate gives a lower mean in some reduced residue
-- statement:
--   Let $N\ne0$, $\alpha\ge0$, $W=\operatorname{primorial}(w)$, and $X=\operatorname{wTrickPrimeScale}(W,N)$, with $w\le\lfloor X/4\rfloor$. Assume $((\log2)/4)X/\log X$ is a lower bound for the number of primes in the selected quarter interval at scale $X$. Then some reduced residue $b$ modulo $W$ has W-tricked prime-weight mean at least $(\alpha/W)((\log2)/4)(X/\log X)\log(\lfloor X/4\rfloor+1)/N$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/WTrickDensity.lean#L341-L399

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

theorem Wikipedia.SzemeredisTheorem.exists_reducedResidue_chebyshev_mean_lower_bound
    {w N : ℕ} [NeZero N] {α : ℝ} (hα : 0 ≤ α)
    (hw : w ≤ wTrickPrimeScale (primorial w) N / 4)
    (hchebyshev :
      log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
          log (wTrickPrimeScale (primorial w) N) ≤
        (#(primesInQuarterInterval
          (wTrickPrimeScale (primorial w) N)) : ℝ)) :
    ∃ b ∈ reducedResidues (primorial w),
      (((α / (primorial w : ℝ)) *
          (log 2 / 4 * (wTrickPrimeScale (primorial w) N : ℝ) /
            log (wTrickPrimeScale (primorial w) N)) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) ≤
        mean
          (wTrickedPrimeWeight α (primorial w) b :
            ZMod N → ℝ) := by sorry
