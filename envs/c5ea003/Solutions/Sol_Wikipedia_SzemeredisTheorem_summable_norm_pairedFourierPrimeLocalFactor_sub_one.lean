-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.summable_norm_pairedFourierPrimeLocalFactor_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:55:22.368405+00:00
-- url     : https://prove2.me/submissions/eb0004fd-4352-4d34-95f3-a082d084e47e

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_UnrestrictedPrimeSupportEulerSeries
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
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
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
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
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_pairedFourierPrimeLocalFactor_sub_one_le_rpow_add_sq

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Euler-product control from square-decaying local errors

The good-prime calculation for the Green--Tao linear-forms system produces
local factors of the form `1 + O(p⁻²)`, outside a finite exceptional set.
This file packages the analytic consequence which is independent of the
particular local-factor formula.

The series of reciprocal prime squares is summable.  Consequently a local
factor with error at most `C / p²` has an absolutely summable error, its
Euler product is multipliable, every finite partial product has an explicit
exponential error bound, and products supported sufficiently far out in the
prime tail are arbitrarily close to one.  A masked version records the
standard operation of replacing finitely many exceptional local factors by
one.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Reciprocal squares are summable over the subtype of natural primes. -/
theorem summable_prime_inv_sq :
    Summable
      (fun p : Nat.Primes =>
        (1 : ℝ) / (p : ℝ) ^ 2) := by
  have h :
      Summable
        (fun p : Nat.Primes =>
          (p : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  refine h.congr fun p => ?_
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [one_div]



namespace HasPrimeSquareError





















end HasPrimeSquareError

/-! ## Removing finitely many exceptional primes -/











/-! ## Masking by a numerical cutoff -/









end Wikipedia.SzemeredisTheorem

end

section



/-!
# The complex arithmetic Euler product as zeta model times correction

`ComplexZetaModelComparison` proves, at every sufficiently large prime, that
the exact affine-system local factor divided by its zeta Euler model is
`1 + O_m(p⁻²)`.  This file promotes that local estimate to an unordered
Euler product.

There are three small points which are made explicit here.

* The exceptional cutoff contains both the finite affine-rank exceptional
  set and the quantitative nonvanishing range for the zeta model.
* The zeta model is in fact nonzero at every prime.  Consequently the
  arithmetic/zeta ratio is defined by honest cancellation at all primes.
* Replacing the finitely many uncontrolled ratios by one gives a globally
  square-decaying family.  The cutoff also makes every remaining ratio
  lie in the radius-`1/2` ball around one, so the masked family is
  pointwise nonzero.  Mathlib's finite-change theorem for products in a
  commutative group-with-zero then restores the exceptional factors.

Combining the resulting correction product with
`cutoffZetaEulerLocalFactor_hasProd` identifies the exact arithmetic prime
product as

`(elementary singular factor) * (completed zeta factor) *
  (convergent arithmetic correction)`.

No nonvanishing assertion is made for the correction without an explicit
nonvanishing hypothesis on the arithmetic local factors: a complex finite
average can in principle vanish.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators

/-! ## Prime-indexed local factors and the common cutoff -/















/-! ## Pointwise nonvanishing of the zeta model -/











/-! ## Square decay and the convergent correction product -/











/-- Only finitely many natural primes lie below a fixed numerical bound.
This is the finite-change input used to restore the exceptional local
ratios. -/
theorem finite_setOf_prime_le (B : ℕ) :
    {p : Nat.Primes | (p : ℕ) ≤ B}.Finite := by
  let e : Nat.Primes ↪ ℕ :=
    ⟨fun p => (p : ℕ), Subtype.coe_injective⟩
  change (e ⁻¹' Set.Iic B).Finite
  exact (Set.finite_Iic B).preimage_embedding e









/-! ## Exact global Euler-product identification -/









end Wikipedia.SzemeredisTheorem

end
/-!
# Unrestricted finite-prime-support Euler series

An Euler product is not the pointwise factorization of the divisor sum in
which every divisor is separately truncated by `d ≤ R`.  This file records
the honest unrestricted object that has such a factorization.

For a prime-indexed family `L p`, put

`E S = ∏ p ∈ S, (L p - 1)`

for a finite set of active primes `S`.  If the local errors are absolutely
summable, then the series over all finite prime supports is absolutely
summable and

`∑' S, E S = ∏' p, L p`.

Thus the unrestricted squarefree prime-support expansion has a rigorous
Euler product, with no divisor cutoff and no conditional rearrangement.
The final section specializes the construction to the exact paired Fourier
local factors.  Comparing this unrestricted series with the original
coordinatewise truncation remains a separate approximation theorem.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Generic absolutely convergent support expansion -/
/-! ## Absolute convergence of paired-Fourier local errors -/

open Wikipedia.SzemeredisTheorem in
/-- The exact paired-Fourier local errors are absolutely summable.  The
essential point is that the positive shift `1/log R` turns the apparent
`p⁻¹` first-order term into `p^(-1-1/log R)`. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    Summable (fun p : Nat.Primes =>
      ‖pairedFourierPrimeLocalFactor
          R forms t u p - 1‖) := by
  let exponent : ℝ :=
    -(Real.log (R : ℝ))⁻¹ - 1
  have hlog : 0 < Real.log (R : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hexponent : exponent < -1 := by
    dsimp only [exponent]
    have hinv : 0 < (Real.log (R : ℝ))⁻¹ :=
      inv_pos.mpr hlog
    linarith
  let majorant : Nat.Primes → ℝ :=
    fun p =>
      (3 * Fintype.card κ : ℝ) *
          (p : ℝ) ^ exponent +
        (4 : ℝ) ^ Fintype.card κ /
          (p : ℝ) ^ 2
  have hmajorant : Summable majorant := by
    have hfirst :
        Summable (fun p : Nat.Primes =>
          (3 * Fintype.card κ : ℝ) *
            (p : ℝ) ^ exponent) :=
      (Nat.Primes.summable_rpow.mpr hexponent).mul_left
        (3 * Fintype.card κ : ℝ)
    have hsquare :
        Summable (fun p : Nat.Primes =>
          (4 : ℝ) ^ Fintype.card κ /
            (p : ℝ) ^ 2) := by
      simpa [div_eq_mul_inv] using
        summable_prime_inv_sq.mul_left
          ((4 : ℝ) ^ Fintype.card κ)
    exact hfirst.add hsquare
  let maskedError : Nat.Primes → ℝ :=
    fun p =>
      if exceptionalPrimeBound forms < (p : ℕ) then
        ‖pairedFourierPrimeLocalFactor
            R forms t u p - 1‖
      else
        0
  have hmasked : Summable maskedError := by
    apply hmajorant.of_nonneg_of_le
    · intro p
      dsimp only [maskedError]
      split_ifs
      · exact norm_nonneg _
      · exact le_rfl
    · intro p
      dsimp only [maskedError, majorant, exponent]
      split_ifs with hp
      · exact
          norm_pairedFourierPrimeLocalFactor_sub_one_le_rpow_add_sq
            hnonzero hindependent hR t u p hp
      · have hfirstNonneg :
            0 ≤
              (3 * Fintype.card κ : ℝ) *
                (p : ℝ) ^
                  (-(Real.log (R : ℝ))⁻¹ - 1) := by
          positivity
        have hsquareNonneg :
            0 ≤
              (4 : ℝ) ^ Fintype.card κ /
                (p : ℝ) ^ 2 := by
          positivity
        linarith
  apply hmasked.congr_cofinite
  filter_upwards
    [(finite_setOf_prime_le
      (exceptionalPrimeBound forms)).eventually_cofinite_notMem]
    with p hp
  have hlarge :
      exceptionalPrimeBound forms < (p : ℕ) := by
    apply Nat.lt_of_not_ge
    intro hle
    apply hp
    exact hle
  simp [maskedError, hlarge]
