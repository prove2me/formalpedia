-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_normalizedSmallPrimeZetaCorrection_sub_one_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:43:16.130249+00:00
-- url     : https://prove2.me/submissions/e758a347-7b17-4b6b-b458-470c04a7aa56

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_normalizedSmallPrimeZetaCorrection_sub_one_le_exp_sum

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

/-- There are at most `w + 1` primes in the small-prime finset. -/
theorem card_smallPrimeFinset_le (w : ℕ) :
    (smallPrimeFinset w).card ≤ w + 1 := by
  calc
    (smallPrimeFinset w).card =
        (Nat.primesLE w).card := by
      simp [smallPrimeFinset]
    _ ≤ (Finset.range (w + 1)).card := by
      apply Finset.card_le_card
      rw [Nat.primesLE_eq_filter_range]
      exact Finset.filter_subset _ _
    _ = w + 1 := by
      simp







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
/-! ## Accumulation over the small primes -/

open Wikipedia.SzemeredisTheorem in
/-- Worst-prime and cardinality simplification of the preceding bound. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (w : ℕ) (t u : κ → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (htclose :
      ∀ p ∈ smallPrimeFinset w, ∀ q,
        ‖SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (t q) - 1‖ ≤ δ)
    (huclose :
      ∀ p ∈ smallPrimeFinset w, ∀ q,
        ‖SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) (u q) - 1‖ ≤ δ) :
    ‖normalizedSmallPrimeZetaCorrection R w t u - 1‖ ≤
      Real.exp
          ((w + 1 : ℕ) *
            (Real.exp
                (6 * (Fintype.card κ : ℝ) * δ ^ 2) -
              1)) -
        1 := by
  have hsum :=
    norm_normalizedSmallPrimeZetaCorrection_sub_one_le_exp_sum
      hR w t u hδ htclose huclose
  refine hsum.trans ?_
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  calc
    (∑ p ∈ smallPrimeFinset w,
        (Real.exp
            ((Fintype.card κ : ℝ) *
              (12 * δ ^ 2 / (p : ℝ))) -
          1)) ≤
        ∑ _p ∈ smallPrimeFinset w,
          (Real.exp
              (6 * (Fintype.card κ : ℝ) * δ ^ 2) -
            1) := by
      apply Finset.sum_le_sum
      intro p _hp
      apply sub_le_sub_right
      apply Real.exp_le_exp.mpr
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast p.prop.two_le
      have hδsq : 0 ≤ δ ^ 2 :=
        sq_nonneg δ
      have hm : 0 ≤ (Fintype.card κ : ℝ) :=
        Nat.cast_nonneg _
      have hpPos : (0 : ℝ) < (p : ℕ) := by
        exact_mod_cast p.prop.pos
      have hlocal :
          12 * δ ^ 2 / (p : ℝ) ≤
            6 * δ ^ 2 := by
        apply (div_le_iff₀ hpPos).2
        nlinarith
      exact
        (mul_le_mul_of_nonneg_left hlocal hm).trans_eq
          (by ring)
    _ =
        ((smallPrimeFinset w).card : ℝ) *
          (Real.exp
              (6 * (Fintype.card κ : ℝ) * δ ^ 2) -
            1) := by
      simp
      ring
    _ ≤
        (w + 1 : ℕ) *
          (Real.exp
              (6 * (Fintype.card κ : ℝ) * δ ^ 2) -
            1) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_smallPrimeFinset_le w
      · exact sub_nonneg.mpr
          (Real.one_le_exp
            (mul_nonneg
              (mul_nonneg (by norm_num)
                (Nat.cast_nonneg _))
              (sq_nonneg δ)))
