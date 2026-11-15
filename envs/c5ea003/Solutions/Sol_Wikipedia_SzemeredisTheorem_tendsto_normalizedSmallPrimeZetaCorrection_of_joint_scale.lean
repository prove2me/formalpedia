-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.tendsto_normalizedSmallPrimeZetaCorrection_of_joint_scale
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:48:42.25047+00:00
-- url     : https://prove2.me/submissions/3b4bacc5-191b-4210-b035-06898905ddc9

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_normalizedSmallPrimeZetaCorrection_sub_one_le_linear

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
/-- Joint `(w,R)` convergence criterion for the normalized small-prime
zeta correction.  It is enough that

`(w + 1) * ((log w / log R) * (1 + 2πT))² → 0`

and that the Fourier parameters eventually remain in the box of radius
`T`.  No relation between `w`, `R`, and `T` beyond this explicit scale is
imposed. -/
theorem solution
    {κ : Type*} [Fintype κ]
    (R w : ℕ → ℕ) (T : ℕ → ℝ)
    (t u : ℕ → κ → ℝ)
    (hR : ∀ᶠ n in atTop, 1 < R n)
    (hw : ∀ᶠ n in atTop, 2 ≤ w n)
    (hT : ∀ᶠ n in atTop, 0 ≤ T n)
    (ht : ∀ᶠ n in atTop, ∀ q, |t n q| ≤ T n)
    (hu : ∀ᶠ n in atTop, ∀ q, |u n q| ≤ T n)
    (hscale :
      Tendsto
        (fun n =>
          (((w n + 1 : ℕ) : ℝ) *
            cutoffPhaseMagnitudeBound
                (R n) (w n) (T n) ^ 2))
        atTop (𝓝 0)) :
    Tendsto
      (fun n =>
        normalizedSmallPrimeZetaCorrection
          (R n) (w n) (t n) (u n))
      atTop (𝓝 1) := by
  let B : ℕ → ℝ := fun n =>
    ((w n + 1 : ℕ) : ℝ) *
      cutoffPhaseMagnitudeBound
          (R n) (w n) (T n) ^ 2
  have hB : Tendsto B atTop (𝓝 0) := by
    simpa only [B] using hscale
  have hBsmall :
      ∀ᶠ n in atTop, B n ≤ 1 :=
    ((tendsto_order.1 hB).2 1 zero_lt_one).mono
      (fun _ hn => hn.le)
  have hphase :
      ∀ᶠ n in atTop,
        cutoffPhaseMagnitudeBound
            (R n) (w n) (T n) ≤ 1 := by
    filter_upwards [hR, hw, hT, hBsmall] with
      n hRn hwn hTn hBsmalln
    have hA0 :
        0 ≤ cutoffPhaseMagnitudeBound
          (R n) (w n) (T n) := by
      rw [cutoffPhaseMagnitudeBound]
      have hlogR :
          0 < Real.log (R n : ℝ) :=
        Real.log_pos (by exact_mod_cast hRn)
      have hlogw :
          0 ≤ Real.log (w n : ℝ) :=
        Real.log_nonneg
          (by exact_mod_cast (Nat.one_le_of_lt hwn))
      positivity
    have hN :
        (1 : ℝ) ≤ ((w n + 1 : ℕ) : ℝ) := by
      exact_mod_cast
        Nat.succ_le_succ (Nat.zero_le (w n))
    have hA2 :
        cutoffPhaseMagnitudeBound
              (R n) (w n) (T n) ^ 2 ≤
          ((w n + 1 : ℕ) : ℝ) *
            cutoffPhaseMagnitudeBound
              (R n) (w n) (T n) ^ 2 := by
      nlinarith [sq_nonneg
        (cutoffPhaseMagnitudeBound
          (R n) (w n) (T n))]
    have hA2one :
        cutoffPhaseMagnitudeBound
            (R n) (w n) (T n) ^ 2 ≤ 1 := by
      apply hA2.trans
      simpa only [B] using hBsmalln
    nlinarith [sq_nonneg
      (cutoffPhaseMagnitudeBound
        (R n) (w n) (T n))]
  have hscaled48 :
      Tendsto
        (fun n => (48 * (Fintype.card κ : ℝ)) * B n)
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul hB :
        Tendsto
          (fun n => (48 * (Fintype.card κ : ℝ)) * B n)
          atTop
          (𝓝 ((48 * (Fintype.card κ : ℝ)) * 0)))
  have hlinear :
      ∀ᶠ n in atTop,
        48 * (Fintype.card κ : ℝ) * B n ≤ 1 := by
    filter_upwards [
      (tendsto_order.1 hscaled48).2 1 zero_lt_one
    ] with n hn
    exact hn.le
  have herror :
      ∀ᶠ n in atTop,
        ‖normalizedSmallPrimeZetaCorrection
              (R n) (w n) (t n) (u n) -
            1‖ ≤
          96 * (Fintype.card κ : ℝ) * B n := by
    filter_upwards
      [hR, hw, hT, ht, hu, hphase, hlinear]
      with n hRn hwn hTn htn hun hphasen hlinearn
    have hn :=
      norm_normalizedSmallPrimeZetaCorrection_sub_one_le_linear
        hRn hwn hTn (t n) (u n) htn hun hphasen
        (by simpa only [B, mul_assoc] using hlinearn)
    simpa only [B, mul_assoc] using hn
  have hscaled96 :
      Tendsto
        (fun n => 96 * (Fintype.card κ : ℝ) * B n)
        atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using
      (tendsto_const_nhds.mul hB :
        Tendsto
          (fun n =>
            (96 * (Fintype.card κ : ℝ)) * B n)
          atTop
          (𝓝 ((96 * (Fintype.card κ : ℝ)) * 0)))
  apply tendsto_iff_norm_sub_tendsto_zero.2
  exact
    squeeze_zero'
      (Eventually.of_forall fun _ => norm_nonneg _)
      herror hscaled96
