-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.abs_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_le_selectedPower
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:11:48.807361+00:00
-- url     : https://prove2.me/submissions/6cbc7f81-4c18-4425-9771-59b9a16b468b

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCyclicBoundaryLimit
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_le_pow
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_abs_normalizedSelbergScale_mul_logSq_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_normalizer_pos

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Geometry of integer affine-form systems

The Goldston--Yıldırım estimate is stated for finite systems of integer
affine forms with nonzero, pairwise non-proportional coefficient vectors and
uniformly bounded coefficients.  This file packages those hypotheses and
verifies them for the Conlon--Fox--Zhao progression forms.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm





end AffineForm











@[simp]
theorem cfzAffineForm_constant {k : ℕ} (q : CFZFormIndex k) :
    (cfzAffineForm q).constant = 0 :=
  rfl

@[simp]
theorem cfzAffineForm_coefficient {k : ℕ}
    (q : CFZFormIndex k) :
    (cfzAffineForm q).coefficient = cfzCoefficient q :=
  rfl









end Wikipedia.SzemeredisTheorem

end

section




/-!
# Small-prime local factors for W-tricked affine forms

If `ψ` is an integer affine form, the affine form occurring after the
`W`-trick is

`x ↦ W * ψ(x) + b`.

At a prime `p ∣ W` this form is identically `b` modulo `p`.  When `b` is a
reduced residue modulo `W`, it is therefore nowhere zero modulo `p`.  This
makes every small-prime avoidance factor, including the complex factor
produced by paired Fourier inversion, exactly one.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem wTrickedAffineForm_constant {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) :
    (wTrickedAffineForm W b ψ).constant =
      (W : ℤ) * ψ.constant + b :=
  rfl

@[simp]
theorem wTrickedAffineForm_coefficient {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) (i : ι) :
    (wTrickedAffineForm W b ψ).coefficient i =
      (W : ℤ) * ψ.coefficient i :=
  rfl



























end Wikipedia.SzemeredisTheorem

end
/-!
# Summed canonical cyclic-to-Euler boundary

The canonical carry partition compares the cyclic paired-divisibility
density with a divisor-independent affine Euler model.  Its pointwise error
is proportional to the paired-divisor LCM divided by the cyclic modulus.
This file sums that estimate over every divisor family selected by a
Boolean CFZ exponent, restores the Selberg normalization, and records a
joint power-scale limit.
-/
open Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Topology
open scoped ArithmeticFunction.Moebius BigOperators
/-! ## Selberg-scaled canonical main terms -/
/-! ## A single polynomial joint scale -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- In the primorial regime the whole scaled boundary is bounded by one
selected-family power `R^(5m)/N`. -/
theorem
    solution
    {k N R w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hR : 2 ≤ R)
    (hb : 0 < b)
    (e : LinearFormsExponent k)
    (hfit :
      2 * R ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤ N) :
    |mean
          (linearFormsProduct k N
            (χ.cyclicMajorant R (primorial w) b) e) -
        χ.selectedCFZCanonicalEulerMainTerm
          (N := N) R (primorial w) b e| ≤
      χ.selectedCFZCanonicalScaledCyclicBoundaryConstant e *
        (R : ℝ) ^
          (5 * Fintype.card (SelectedCFZFormIndex e)) /
        (N : ℝ) := by
  let m := Fintype.card (SelectedCFZFormIndex e)
  have hraw :=
    χ.abs_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerMainTerm_le_pow
      (W := primorial w) hk (by omega : 1 < R) hb e hfit
  have hbase :
      |normalizedSelbergScale
          χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| ≤
        χ.normalizer⁻¹ * (1 + Real.log R) :=
    χ.abs_normalizedSelbergScale_mul_logSq_le hR w
  have hbaseNonneg :
      0 ≤
        |normalizedSelbergScale
            χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| := by
    positivity
  have hlogNonneg : 0 ≤ 1 + Real.log R := by
    have hlog :
        0 ≤ Real.log R :=
      (Real.log_pos
        (by exact_mod_cast hR : (1 : ℝ) < R)).le
    linarith
  have hlogLe : 1 + Real.log R ≤ (R : ℝ) := by
    have hRpos : (0 : ℝ) < R := by positivity
    have hlog := Real.log_le_sub_one_of_pos hRpos
    linarith
  have hinvNonneg : 0 ≤ χ.normalizer⁻¹ :=
    inv_nonneg.mpr χ.normalizer_pos.le
  have hupperBaseNonneg :
      0 ≤ χ.normalizer⁻¹ * (1 + Real.log R) :=
    mul_nonneg hinvNonneg hlogNonneg
  have hprefactor :
      |normalizedSelbergScale
          χ.normalizer R (primorial w)| ^ m *
          |Real.log R ^ 2| ^ m ≤
        χ.normalizer⁻¹ ^ m * (R : ℝ) ^ m := by
    calc
      |normalizedSelbergScale
            χ.normalizer R (primorial w)| ^ m *
          |Real.log R ^ 2| ^ m =
        (|normalizedSelbergScale
              χ.normalizer R (primorial w)| *
            |Real.log R ^ 2|) ^ m := by
        rw [mul_pow]
      _ ≤
        (χ.normalizer⁻¹ * (1 + Real.log R)) ^ m :=
          pow_le_pow_left₀ hbaseNonneg hbase m
      _ ≤ (χ.normalizer⁻¹ * (R : ℝ)) ^ m := by
        exact
          pow_le_pow_left₀ hupperBaseNonneg
            (mul_le_mul_of_nonneg_left hlogLe hinvNonneg) m
      _ = χ.normalizer⁻¹ ^ m * (R : ℝ) ^ m := by
        rw [mul_pow]
  have hinner :
      0 ≤
        (selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          (R : ℝ) ^ (2 * m) *
          (R : ℝ) ^ (2 * m) /
          (N : ℝ) := by
    positivity
  calc
    |mean
          (linearFormsProduct k N
            (χ.cyclicMajorant R (primorial w) b) e) -
        χ.selectedCFZCanonicalEulerMainTerm
          (N := N) R (primorial w) b e| ≤
      |normalizedSelbergScale
          χ.normalizer R (primorial w)| ^ m *
        |Real.log R ^ 2| ^ m *
        ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          (R : ℝ) ^ (2 * m) *
          (R : ℝ) ^ (2 * m) /
          (N : ℝ)) := by
      simpa only [m] using hraw
    _ ≤
      (χ.normalizer⁻¹ ^ m * (R : ℝ) ^ m) *
        ((selectedCFZCanonicalCyclicBoundaryConstant e : ℝ) *
          (R : ℝ) ^ (2 * m) *
          (R : ℝ) ^ (2 * m) /
          (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hprefactor hinner
    _ =
      χ.selectedCFZCanonicalScaledCyclicBoundaryConstant e *
        (R : ℝ) ^ (5 * m) / (N : ℝ) := by
      unfold selectedCFZCanonicalScaledCyclicBoundaryConstant
      rw [show 5 * m = m + 2 * m + 2 * m by omega,
        pow_add, pow_add]
      ring
    _ = _ := by rfl
