-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_forall_pos_exists_reducedResidue_mean_ge
-- name    : Wikipedia.SzemeredisTheorem.eventually_forall_pos_exists_reducedResidue_mean_ge
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:54:13.653428+00:00
-- url     : https://prove2.me/theorems/5475230e-cd90-4ffa-befc-07cb1168256b
-- title:
--   A reduced residue with positive prime-weight mean exists at every large modulus
-- statement:
--   Fix a natural primorial parameter $w$ and a real scale $\alpha>0$, and put $W=\operatorname{primorial}(w)$. For every sufficiently large positive natural modulus $N$, some reduced residue $b<W$ with $\gcd(W,b)=1$ satisfies
--
--   $$
--   \mathbb E_{x\in\mathbb Z/N\mathbb Z}f_{\alpha,W,b}(x)
--   \ge\frac{\alpha\log2}{128}.
--   $$
--
--   The residue may depend on $N$; primality of $N$ is not required.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Primes/WTrickDensity.lean#L633-L681

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

theorem Wikipedia.SzemeredisTheorem.eventually_forall_pos_exists_reducedResidue_mean_ge
    {w : ℕ} {α : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop,
      ∀ hN : 0 < N,
        letI : NeZero N := ⟨hN.ne'⟩
        ∃ b ∈ reducedResidues (primorial w),
          α * log 2 / 128 ≤
            mean
              (wTrickedPrimeWeight α (primorial w) b :
                ZMod N → ℝ) := by sorry
