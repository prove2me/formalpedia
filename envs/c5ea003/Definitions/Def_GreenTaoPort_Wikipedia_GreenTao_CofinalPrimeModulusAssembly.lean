-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_CofinalPrimeModulusAssembly
-- name    : GreenTaoPort_Wikipedia_GreenTao_CofinalPrimeModulusAssembly
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:00:00.680979+00:00
-- url     : https://prove2.me/theorems/c5251f6b-f292-4656-8e84-0217bb065001
-- title:
--   Uniform progression counts along cofinal prime moduli
-- statement:
--   For every progression length $k\ge3$, this predicate fixes positive real constants $\alpha,c$ and a positive integer $W$. After these constants are fixed, every natural threshold $M_0$ must admit an $M\ge M_0$ for which $M+1$ is prime and some residue $b<W$ satisfies
--
--   $$
--   c\le \operatorname{APCount}_k\!\left(\mathbb Z/(M+1)\mathbb Z,\,f_{\alpha,W,b}\right).
--   $$
--
--   Here $f_{\alpha,W,b}$ is the localized $W$-tricked prime weight and the count is the normalized cyclic progression count. The residue may depend on the chosen modulus; the scale, period, and positive lower bound may not. Thus only arbitrarily large prime moduli are required, rather than every sufficiently large modulus.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/CofinalPrimeModulusAssembly.lean#L27-L40

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Assembly
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrickDensity
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Green--Tao assembly along cofinal prime moduli

The transference layer uses invertibility of the nonzero progression
coefficients and therefore naturally assumes that the cyclic modulus is
coprime to `(k - 1)!`.  Choosing an arbitrarily large prime modulus larger
than `k` supplies that hypothesis.  The previous assembly-facing predicate
asked for a count lower bound at *every* sufficiently large modulus, which
was stronger than both the proof and the transference theorem require.

This file records the exact cofinal prime-modulus interface.  Cofinality is
enough for diagonal exclusion because the logarithmic diagonal estimate is
eventual: simply choose the prime modulus after its threshold.  The
Chebyshev reduced-residue argument also holds at every sufficiently large
modulus, so it restricts to the same cofinal prime family without loss.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter

/-! ## Cofinal prime count lower bounds -/

/-- The exact count output needed along arbitrarily large prime cyclic
moduli.  All W-trick parameters and the positive count lower bound are
fixed before the lower bound on the modulus is supplied. -/
def HasCofinalPrimeWTrickedPrimeProgressionCountLower : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ∃ (α : ℝ) (W : ℕ) (c : ℝ),
      0 < α ∧ 0 < W ∧ 0 < c ∧
        ∀ M₀ : ℕ,
          ∃ M : ℕ,
            M₀ ≤ M ∧ Nat.Prime (M + 1) ∧
              ∃ b : ℕ, b < W ∧
                c ≤
                  cyclicAPCount k (M + 1)
                    (wTrickedPrimeWeight α W b)







/-! ## Standard cutoff and reduced-residue selection -/









end Wikipedia.SzemeredisTheorem


