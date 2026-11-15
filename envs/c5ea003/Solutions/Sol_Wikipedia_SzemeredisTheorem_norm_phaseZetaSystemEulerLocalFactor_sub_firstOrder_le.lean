-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_phaseZetaSystemEulerLocalFactor_sub_firstOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:53:30.018542+00:00
-- url     : https://prove2.me/submissions/e76d6fa5-45d2-45ae-b3a9-3f8b028a2cd5

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
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
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_fintypeProd_sub_combinedFirstOrder_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_phasePairZetaEulerLocalModel_sub_firstOrder_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_phasePairZetaEulerLocalModel_sub_one_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Comparing Fourier local factors with zeta Euler models

For one pair of Fourier phases `z, w` and `r = 1 / p`, the first-order
arithmetic model is

`1 - r * (z + w - z * w)`.

The corresponding local factor of the zeta quotient is

`((1 - r * z) * (1 - r * w)) / (1 - r * z * w)`.

Their difference has the exact factorization

`r² z w (1 - z) (1 - w) / (1 - r z w)`.

At a prime, the Fourier phases have norm at most one.  The denominator is
therefore bounded below by `1/2`, and the difference is at most `8 / p²`,
uniformly in both Fourier parameters.

For a finite system of `m` forms, expanding the product separates the sum
of the singleton errors from supports of size at least two.  Above `p ≥ 7`,
the latter are bounded by `49 * 2^m / p²`.  This gives an explicit
finite-system comparison with the combined first-order model, and hence a
ratio comparison above the additional stability cutoff `p ≥ 6m`.

The final section combines this result with the affine rank-two calculation
from `ComplexLocalFactorControl`.  It remains entirely local: no infinite
prime-product identity and no multivariate Fourier integration is asserted.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## A generic finite-product second-order remainder -/
/-! ## One paired phase -/
/-! ## Exact cpow coordinates -/
/-! ## Finite systems -/

open Wikipedia.SzemeredisTheorem in
/-- The product of the per-form zeta factors differs from the combined
first-order model by `O_m(p⁻²)`. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {p : ℕ} (hp : p.Prime) (hseven : 7 ≤ p)
    (z w : κ → ℂ)
    (hz : ∀ q, ‖z q‖ ≤ 1)
    (hw : ∀ q, ‖w q‖ ≤ 1) :
    ‖phaseZetaSystemEulerLocalFactor p z w -
        complexFirstOrderLocalModel p
          (fun q => z q + w q - z q * w q)‖ ≤
      complexZetaModelDifferenceConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  classical
  have hpR : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hsevenR : (7 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hseven
  have habstract :=
    norm_fintypeProd_sub_combinedFirstOrder_le
      (Q := fun q =>
        phasePairZetaEulerLocalModel p (z q) (w q))
      (a := fun q => z q + w q - z q * w q)
      ((p : ℂ)⁻¹)
      (B := (7 : ℝ) / (p : ℝ))
      (D := (8 : ℝ) / (p : ℝ) ^ 2)
      (by positivity)
      (by
        rw [div_le_one hpR]
        exact hsevenR)
      (fun q =>
        norm_phasePairZetaEulerLocalModel_sub_one_le
          hp (hz q) (hw q))
      (fun q => by
        simpa [phasePairFirstOrderLocalModel] using
          (norm_phasePairZetaEulerLocalModel_sub_firstOrder_le
            hp (hz q) (hw q)))
  have hright :
      Fintype.card κ * ((8 : ℝ) / (p : ℝ) ^ 2) +
          (2 : ℝ) ^ Fintype.card κ *
            ((7 : ℝ) / (p : ℝ)) ^ 2 =
        complexZetaModelDifferenceConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
    rw [complexZetaModelDifferenceConstant]
    ring
  have hleft :
      (1 - (p : ℂ)⁻¹ *
          ∑ q : κ, (z q + w q - z q * w q)) =
        complexFirstOrderLocalModel p
          (fun q => z q + w q - z q * w q) := by
    rw [complexFirstOrderLocalModel]
    simp only [div_eq_mul_inv]
    ring
  rw [phaseZetaSystemEulerLocalFactor, ← hleft]
  exact habstract.trans_eq hright
