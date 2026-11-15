-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HasCofinalPrimeWTrickedPrimeProgressionCountLower.toMass
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:00:31.249097+00:00
-- url     : https://prove2.me/submissions/ff4a6a7a-3689-497e-849b-24f0986a6a6d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Assembly
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_CofinalPrimeModulusAssembly
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrickDensity
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
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
import Mathlib.Data.Nat.Prime.Infinite
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_mul_log_pow_lt_linear
import Theorems.Thm_Wikipedia_SzemeredisTheorem_wTrickedPrimeWeight_offDiagMass_pos_of_count_lower

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Negligibility of diagonal progressions

The relative-counting argument produces a positive lower bound for the
normalized count of cyclic progressions.  To extract a progression with
nonzero common difference, that lower bound must dominate the contribution
of the constant progressions.

For the W-tricked prime weight the pointwise height is at most a fixed
multiple of `log N`.  Since every fixed power of `log N` is `o(N)`, the
diagonal contribution is eventually smaller than any fixed positive
progression-count lower bound.  This file records that elementary bridge
without imposing any sieve or transference hypotheses.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter















/-- In particular, the crude W-tricked height raised to any fixed power is
eventually negligible compared with a fixed positive count lower bound. -/
theorem eventually_wTrickedPrimeWeight_height_pow_lt_linear
    (α c : ℝ) (k : ℕ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop,
      (2 * α * Real.log (N : ℝ)) ^ k <
        (N : ℝ) * c := by
  simpa [mul_assoc] using
    eventually_mul_log_pow_lt_linear (2 * α) c k hc

/-! ## Asymptotic final interface -/







end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open Filter
/-! ## Cofinal prime count lower bounds -/

/-- Cofinal positive count lower bounds imply positive off-diagonal
progression mass.  The selected prime is taken beyond the logarithmic
height threshold and the elementary `W+b≤N` threshold. -/
theorem solution
    (hcount :
      HasCofinalPrimeWTrickedPrimeProgressionCountLower) :
    HasPrimeProgressionMass := by
  intro k hk
  obtain ⟨α, W, c, hα, hW, hc, hcofinal⟩ :=
    hcount k hk
  have heventualHeight :=
    eventually_wTrickedPrimeWeight_height_pow_lt_linear
      α c k hc
  rw [eventually_atTop] at heventualHeight
  obtain ⟨Nheight, hheightFrom⟩ := heventualHeight
  obtain ⟨M, hMlarge, _hprime, b, hb, hcountLower⟩ :=
    hcofinal (max (2 * W) Nheight)
  have htwoW : 2 * W ≤ M :=
    (le_max_left (2 * W) Nheight).trans hMlarge
  have hNheight : Nheight ≤ M + 1 :=
    (le_max_right (2 * W) Nheight).trans
      (hMlarge.trans (Nat.le_succ M))
  have hWB : W + b ≤ M + 1 := by
    omega
  have hheight :
      (2 * α * Real.log ((M + 1 : ℕ) : ℝ)) ^ k <
        ((M + 1 : ℕ) : ℝ) * c :=
    hheightFrom (M + 1) hNheight
  refine ⟨M, α, W, b, hα, hW, ?_⟩
  exact
    wTrickedPrimeWeight_offDiagMass_pos_of_count_lower
      (by omega) hα.le hW (by omega) hWB
      hcountLower hheight
