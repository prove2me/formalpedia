-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_divisorMultiplicativePhase_sub_one_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:23:50.284776+00:00
-- url     : https://prove2.me/submissions/cd454f46-a159-4139-93a2-0d87086b983b

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_cutoffPhaseExponent_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


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

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology

/-! ## One paired phase -/













/-! ## A finite system at one prime -/







/-! ## Accumulation over the small primes -/









/-! ## The actual cutoff phases -/





/-- A cutoff phase is close to one when its exponent bound is at most one. -/
theorem norm_cutoffMultiplicativePhase_sub_one_le
    {x t T : ℝ} (hx : 0 ≤ x)
    (ht : |t| ≤ T)
    (hsmall : x * (1 + 2 * Real.pi * T) ≤ 1) :
    ‖SmoothSieveCutoff.cutoffMultiplicativePhase x t - 1‖ ≤
      2 * x * (1 + 2 * Real.pi * T) := by
  have hexponent :=
    norm_cutoffPhaseExponent_le hx ht
  rw [SmoothSieveCutoff.cutoffMultiplicativePhase]
  exact
    (Complex.norm_exp_sub_one_le
      (hexponent.trans hsmall)).trans
      (by nlinarith)





/-! ## Linearized control and joint convergence -/







end Wikipedia.SzemeredisTheorem

end
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

open Wikipedia.SzemeredisTheorem in
/-- Uniform actual-phase estimate on all primes at most `w`. -/
theorem solution
    {R w : ℕ} (hR : 1 < R) (hw : 2 ≤ w)
    {T : ℝ} (hT : 0 ≤ T)
    {p : Nat.Primes} (hpw : (p : ℕ) ≤ w)
    {t : ℝ} (ht : |t| ≤ T)
    (hsmall : cutoffPhaseMagnitudeBound R w T ≤ 1) :
    ‖SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) t - 1‖ ≤
      2 * cutoffPhaseMagnitudeBound R w T := by
  have hlogR :
      0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  have hlogp :
      0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg
      (by exact_mod_cast p.prop.one_le)
  have hlogw :
      0 ≤ Real.log (w : ℝ) :=
    Real.log_nonneg
      (by exact_mod_cast (Nat.one_le_of_lt hw))
  have hlogle :
      Real.log (p : ℝ) ≤ Real.log (w : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast p.prop.pos)
      (by exact_mod_cast hpw)
  have hx :
      0 ≤ Real.log (p : ℝ) / Real.log R :=
    div_nonneg hlogp hlogR.le
  have hxle :
      Real.log (p : ℝ) / Real.log R ≤
        Real.log (w : ℝ) / Real.log R :=
    div_le_div_of_nonneg_right hlogle hlogR.le
  have hcoef :
      0 ≤ 1 + 2 * Real.pi * T := by
    positivity
  have hphaseBound :
      (Real.log (p : ℝ) / Real.log R) *
          (1 + 2 * Real.pi * T) ≤
        cutoffPhaseMagnitudeBound R w T := by
    rw [cutoffPhaseMagnitudeBound]
    exact mul_le_mul_of_nonneg_right hxle hcoef
  rw [SmoothSieveCutoff.divisorMultiplicativePhase]
  refine
    (norm_cutoffMultiplicativePhase_sub_one_le
      hx ht (hphaseBound.trans hsmall)).trans ?_
  calc
    2 *
          (Real.log (p : ℝ) / Real.log R) *
          (1 + 2 * Real.pi * T) =
        2 *
          ((Real.log (p : ℝ) / Real.log R) *
            (1 + 2 * Real.pi * T)) := by
      ring
    _ ≤ 2 * cutoffPhaseMagnitudeBound R w T :=
      mul_le_mul_of_nonneg_left hphaseBound (by norm_num)
