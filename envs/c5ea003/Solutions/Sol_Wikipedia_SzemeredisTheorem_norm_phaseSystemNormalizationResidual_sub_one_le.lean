-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_phaseSystemNormalizationResidual_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:31:12.286089+00:00
-- url     : https://prove2.me/submissions/bd03ce50-6643-4949-8c07-90f3116dbca9

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_phasePairNormalizationResidual_sub_one_le

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



/-- The normalized system residual factors into the normalized residuals
of its paired coordinates. -/
theorem phaseSystemNormalizationResidual_eq_prod
    {κ : Type*} [Fintype κ]
    (p : ℕ) (z v : κ → ℂ) :
    phaseSystemNormalizationResidual p z v =
      ∏ q, phasePairNormalizationResidual p (z q) (v q) := by
  rw [phaseSystemNormalizationResidual,
    unshiftedZetaSystemLocalFactor,
    phaseZetaSystemEulerLocalFactor,
    ← Finset.prod_inv_distrib]
  have hconst :
      (1 - (p : ℂ)⁻¹) ^ Fintype.card κ =
        ∏ _q : κ, (1 - (p : ℂ)⁻¹) := by
    simp
  rw [hconst, ← Finset.prod_mul_distrib]
  simp [phasePairNormalizationResidual]



/-! ## Accumulation over the small primes -/









/-! ## The actual cutoff phases -/











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

open Wikipedia.SzemeredisTheorem in
/-- Accumulating the quadratic pair estimate across a finite system gives
an explicit exponential error bound. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {p : ℕ} (hp : p.Prime)
    (z v : κ → ℂ)
    (hz : ∀ q, ‖z q‖ ≤ 1)
    (hv : ∀ q, ‖v q‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hzclose : ∀ q, ‖z q - 1‖ ≤ δ)
    (hvclose : ∀ q, ‖v q - 1‖ ≤ δ) :
    ‖phaseSystemNormalizationResidual p z v - 1‖ ≤
      Real.exp
          ((Fintype.card κ : ℝ) *
            (12 * δ ^ 2 / (p : ℝ))) -
        1 := by
  rw [phaseSystemNormalizationResidual_eq_prod]
  have hbase :=
    (Finset.univ : Finset κ).norm_prod_one_add_sub_one_le
      (fun q =>
        phasePairNormalizationResidual p (z q) (v q) - 1)
  have heq :
      (fun q : κ =>
        1 +
          (phasePairNormalizationResidual p
            (z q) (v q) - 1)) =
        fun q =>
          phasePairNormalizationResidual p (z q) (v q) := by
    funext q
    ring
  rw [heq] at hbase
  have hsum :
      (∑ q : κ,
          ‖phasePairNormalizationResidual p
              (z q) (v q) - 1‖) ≤
        (Fintype.card κ : ℝ) *
          (12 * δ ^ 2 / (p : ℝ)) := by
    calc
      (∑ q : κ,
          ‖phasePairNormalizationResidual p
              (z q) (v q) - 1‖) ≤
          ∑ _q : κ, 12 * δ ^ 2 / (p : ℝ) := by
        apply Finset.sum_le_sum
        intro q _hq
        exact
          norm_phasePairNormalizationResidual_sub_one_le
            hp (hz q) (hv q) hδ
            (hzclose q) (hvclose q)
      _ =
          (Fintype.card κ : ℝ) *
            (12 * δ ^ 2 / (p : ℝ)) := by
        simp
  exact hbase.trans
    (sub_le_sub_right
      (Real.exp_le_exp.mpr hsum) 1)
