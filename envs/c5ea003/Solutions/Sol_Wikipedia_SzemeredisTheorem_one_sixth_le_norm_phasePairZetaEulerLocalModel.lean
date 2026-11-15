-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.one_sixth_le_norm_phasePairZetaEulerLocalModel
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:26:26.563747+00:00
-- url     : https://prove2.me/submissions/1f16a459-9f76-4f00-a426-02b8e8cd4d39

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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrectionLimit
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_one_half_le_norm_phasePairZetaDenominator
import Theorems.Thm_Wikipedia_SzemeredisTheorem_one_half_le_norm_phaseZetaNumerator

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Quantitative convergence of the W-tricked Euler correction

`WTrickedEulerCorrection` writes the normalized finite small-prime
correction as

`∏_{p ≤ w} ((1 - p⁻¹)^m * Z_p(z, v)⁻¹)`.

This file controls that product when every phase is close to one.  The
important cancellation is

`z + v - z v - 1 = -(1-z)(1-v)`,

so the perturbation is quadratic in the phase error.  We first prove a
one-pair bound valid at every prime, then accumulate it over the finite
form system and over all primes at most `w`.
-/
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators Topology
/-! ## One paired phase -/

open Wikipedia.SzemeredisTheorem in
/-- A paired zeta factor has a uniform lower norm bound at every prime. -/
theorem solution
    {p : ℕ} (hp : p.Prime)
    {z v : ℂ} (hz : ‖z‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    (1 : ℝ) / 6 ≤
      ‖phasePairZetaEulerLocalModel p z v‖ := by
  have hzhalf :=
    one_half_le_norm_phaseZetaNumerator hp hz
  have hvhalf :=
    one_half_le_norm_phaseZetaNumerator hp hv
  have hdhalf :=
    one_half_le_norm_phasePairZetaDenominator hp hz hv
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hsmall :
      ‖(p : ℂ)⁻¹ * z * v‖ ≤ (1 : ℝ) / 2 := by
    calc
      ‖(p : ℂ)⁻¹ * z * v‖ =
          (1 / (p : ℝ)) * ‖z‖ * ‖v‖ := by
        rw [norm_mul, norm_mul, norm_inv,
          Complex.norm_natCast]
        ring
      _ ≤ (1 / (p : ℝ)) * 1 * 1 := by
        gcongr
      _ ≤ (1 : ℝ) / 2 := by
        simp only [mul_one]
        rw [div_le_iff₀ hpR]
        have hp2R : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast hp.two_le
        nlinarith
  have hdUpper :
      ‖1 - (p : ℂ)⁻¹ * z * v‖ ≤
        (3 : ℝ) / 2 := by
    calc
      ‖1 - (p : ℂ)⁻¹ * z * v‖ ≤
          ‖(1 : ℂ)‖ +
            ‖(p : ℂ)⁻¹ * z * v‖ :=
        norm_sub_le _ _
      _ ≤ (3 : ℝ) / 2 := by
        rw [norm_one]
        linarith
  have hdPos :
      0 < ‖1 - (p : ℂ)⁻¹ * z * v‖ :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le
      hdhalf
  rw [phasePairZetaEulerLocalModel,
    Complex.norm_div, norm_mul]
  rw [le_div_iff₀ hdPos]
  nlinarith [norm_nonneg
    (1 - (p : ℂ)⁻¹ * z),
    norm_nonneg (1 - (p : ℂ)⁻¹ * v)]
