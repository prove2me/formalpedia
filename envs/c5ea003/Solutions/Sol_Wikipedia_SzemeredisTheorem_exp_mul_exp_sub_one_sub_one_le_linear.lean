-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exp_mul_exp_sub_one_sub_one_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:52:11.960737+00:00
-- url     : https://prove2.me/submissions/5012ed97-1f4d-4397-9257-9f7cc1381b57

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
/-! ## A finite system at one prime -/
/-! ## Accumulation over the small primes -/
/-! ## The actual cutoff phases -/
/-! ## Linearized control and joint convergence -/

open Wikipedia.SzemeredisTheorem in
/-- A two-level exponential error is linear in its inner exponent in the
range needed below.  The single smallness condition also forces the
inner exponent to lie in the unit interval. -/
theorem solution
    {N a : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a)
    (hsmall : 2 * N * a ≤ 1) :
    Real.exp (N * (Real.exp a - 1)) - 1 ≤
      4 * N * a := by
  have hN0 : 0 ≤ N := hN.trans' zero_le_one
  have ha_le : a ≤ 2 * N * a := by
    calc
      a = 1 * a := by ring
      _ ≤ (2 * N) * a := by
        apply mul_le_mul_of_nonneg_right _ ha
        nlinarith
      _ = 2 * N * a := by ring
  have ha_one : a ≤ 1 :=
    ha_le.trans hsmall
  have habs : |a| ≤ 1 := by
    rw [abs_of_nonneg ha]
    exact ha_one
  have hinner0 : 0 ≤ Real.exp a - 1 :=
    sub_nonneg.mpr (Real.one_le_exp ha)
  have hinner :
      Real.exp a - 1 ≤ 2 * a := by
    calc
      Real.exp a - 1 =
          |Real.exp a - 1| := by
        rw [abs_of_nonneg hinner0]
      _ ≤ 2 * |a| :=
        Real.abs_exp_sub_one_le habs
      _ = 2 * a := by
        rw [abs_of_nonneg ha]
  have houter0 :
      0 ≤ N * (Real.exp a - 1) :=
    mul_nonneg hN0 hinner0
  have houter_one :
      N * (Real.exp a - 1) ≤ 1 := by
    calc
      N * (Real.exp a - 1) ≤
          N * (2 * a) :=
        mul_le_mul_of_nonneg_left hinner hN0
      _ = 2 * N * a := by ring
      _ ≤ 1 := hsmall
  have houter_abs :
      |N * (Real.exp a - 1)| ≤ 1 := by
    rw [abs_of_nonneg houter0]
    exact houter_one
  have houterExp0 :
      0 ≤ Real.exp (N * (Real.exp a - 1)) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp houter0)
  calc
    Real.exp (N * (Real.exp a - 1)) - 1 =
        |Real.exp (N * (Real.exp a - 1)) - 1| := by
      rw [abs_of_nonneg houterExp0]
    _ ≤ 2 * |N * (Real.exp a - 1)| :=
      Real.abs_exp_sub_one_le houter_abs
    _ = 2 * (N * (Real.exp a - 1)) := by
      rw [abs_of_nonneg houter0]
    _ ≤ 2 * (N * (2 * a)) := by
      gcongr
    _ = 4 * N * a := by ring
