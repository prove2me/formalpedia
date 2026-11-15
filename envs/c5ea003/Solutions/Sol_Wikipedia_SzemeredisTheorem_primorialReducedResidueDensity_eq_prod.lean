-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.primorialReducedResidueDensity_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:31:12.098292+00:00
-- url     : https://prove2.me/submissions/f3ce3065-f3dc-4f6f-b4cf-d4fa53e1a1d3

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# The finite Euler correction at W-tricked primes

For `W = primorial w`, every arithmetic local factor at a prime `p ≤ w`
is one.  Relative to the universal zeta Euler model, its arithmetic/zeta
ratio is therefore the inverse zeta factor.  This file packages the exact
finite product of those inverses and compares it with the Selberg
normalization `(φ(W) / W)^m`.

The comparison is exact: the normalized correction is a finite product of
the ratios between the unshifted local model `(1 - p⁻¹)^m` and the shifted
Fourier-zeta local model.  Thus the only remaining small-prime asymptotic is
to show that these finitely many shifted model factors approach their
unshifted values in the chosen joint `w, R` regime.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Backport of `primeFactors_primorial` from Mathlib's
`NumberTheory/Primorial.lean` at `0df444a360eaa60ab8c11dca51a86af692955474`. -/
private theorem primeFactors_primorial_compat (w : ℕ) :
    (primorial w).primeFactors = Nat.primesLE w := by
  simpa only [primorial_eq_prod_primesLE] using
    (Nat.primeFactors_prod (s := Nat.primesLE w)
      (fun _ hp => Nat.prime_of_mem_primesLE hp))

















/-! ## The parallel first-order correction -/









/-! ## Exact comparison with the totient normalization -/















/-! ## The unshifted phase model -/



















end Wikipedia.SzemeredisTheorem

end
/-!
# The finite Euler correction at W-tricked primes

For `W = primorial w`, every arithmetic local factor at a prime `p ≤ w`
is one.  Relative to the universal zeta Euler model, its arithmetic/zeta
ratio is therefore the inverse zeta factor.  This file packages the exact
finite product of those inverses and compares it with the Selberg
normalization `(φ(W) / W)^m`.

The comparison is exact: the normalized correction is a finite product of
the ratios between the unshifted local model `(1 - p⁻¹)^m` and the shifted
Fourier-zeta local model.  Thus the only remaining small-prime asymptotic is
to show that these finitely many shifted model factors approach their
unshifted values in the chosen joint `w, R` regime.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## The parallel first-order correction -/
/-! ## Exact comparison with the totient normalization -/

open Wikipedia.SzemeredisTheorem in
/-- Euler's totient product formula for a primorial, in the exact complex
form used by the Fourier-zeta factors. -/
theorem solution
    (w : ℕ) :
    primorialReducedResidueDensity w =
      ∏ p ∈ smallPrimeFinset w,
        (1 - (p : ℂ)⁻¹) := by
  have hW : primorial w ≠ 0 :=
    (primorial_pos w).ne'
  have hq :
      (((primorial w).totient : ℚ) /
          (primorial w : ℚ)) =
        ∏ p ∈ Nat.primesLE w,
          (1 - (p : ℚ)⁻¹) := by
    rw [Nat.totient_eq_mul_prod_factors (primorial w),
      primeFactors_primorial_compat]
    have hWq : (primorial w : ℚ) ≠ 0 := by
      exact_mod_cast hW
    field_simp [hWq]
  have hprod :
      (∏ p ∈ smallPrimeFinset w,
          (1 - (p : ℂ)⁻¹)) =
        ∏ p ∈ Nat.primesLE w,
          (1 - (p : ℂ)⁻¹) := by
    rw [smallPrimeFinset, Finset.prod_map]
    exact Finset.prod_attach
      (Nat.primesLE w)
      (fun p : ℕ => 1 - (p : ℂ)⁻¹)
  rw [primorialReducedResidueDensity, hprod]
  have hc :=
    congrArg (algebraMap ℚ ℂ) hq
  simpa using hc
