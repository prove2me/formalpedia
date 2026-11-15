-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_pairedFourierArithmeticToZetaLocalRatio_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:57:46.665321+00:00
-- url     : https://prove2.me/submissions/4ce65552-1503-4f24-9969-c8ed9a39d9e8

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_pairedFourierLocalFactor_sub_zetaModel_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_one_fourth_le_norm_fourierZetaSystemEulerLocalFactor

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
/-! ## Direct arithmetic/zeta comparison -/

open Wikipedia.SzemeredisTheorem in
/-- The direct arithmetic/zeta ratio is `1 + O_m(p⁻²)` above the explicit
rank, size, and nonvanishing cutoffs. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R p : ℕ} [NeZero p] (hR : 2 ≤ R) (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (hcut :
      complexZetaModelNonzeroCutoff
          (Fintype.card κ) ≤ p)
    (t u : κ → ℝ) :
    ‖pairedFourierArithmeticToZetaLocalRatio
          R p forms t u - 1‖ ≤
      complexArithmeticZetaRatioErrorConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  let zeta :=
    fourierZetaSystemEulerLocalFactor R p t u
  have hzetaQuarter :
      (1 : ℝ) / 4 ≤ ‖zeta‖ := by
    exact one_fourth_le_norm_fourierZetaSystemEulerLocalFactor
      hR hp hcut t u
  have hzetaPos : 0 < ‖zeta‖ :=
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le
      hzetaQuarter
  have hcomparison :
      complexZetaModelComparisonCutoff
          (Fintype.card κ) ≤ p :=
    (Nat.le_max_left _ _).trans hcut
  have hdiff :
      ‖pairedFourierLocalFactor R p forms t u -
          zeta‖ ≤
        complexArithmeticZetaDifferenceConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
    simpa [zeta] using
      norm_pairedFourierLocalFactor_sub_zetaModel_le
        hnonzero hindependent hR hp hlarge
        ((Nat.le_max_left 7
          (6 * Fintype.card κ)).trans hcomparison)
        t u
  have hzetaNe : zeta ≠ 0 :=
    norm_pos_iff.mp hzetaPos
  rw [pairedFourierArithmeticToZetaLocalRatio,
    div_sub_one hzetaNe, Complex.norm_div]
  calc
    ‖pairedFourierLocalFactor R p forms t u - zeta‖ /
          ‖zeta‖ ≤
        4 *
          ‖pairedFourierLocalFactor R p forms t u - zeta‖ := by
      rw [div_le_iff₀ hzetaPos]
      have hnonneg :
          0 ≤
            ‖pairedFourierLocalFactor R p forms t u - zeta‖ :=
        norm_nonneg _
      nlinarith
    _ ≤
        4 *
          (complexArithmeticZetaDifferenceConstant
              (Fintype.card κ) /
            (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiff (by norm_num)
    _ =
        complexArithmeticZetaRatioErrorConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
      rw [complexArithmeticZetaRatioErrorConstant]
      ring
