-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.eventually_two_mul_cfzDivisorBox_le_of_boundaryPower_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:51:10.449487+00:00
-- url     : https://prove2.me/submissions/40be0986-d744-4265-b211-b2d720ebc0ae

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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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

open Wikipedia.SzemeredisTheorem in
/-- The power-ratio schedule itself eventually forces the single global
divisor-box fit condition. -/
theorem solution
    {k : ℕ}
    (hk : 2 ≤ k)
    (R Nseq : ℕ → ℕ)
    (hN : ∀ n, Nseq n ≠ 0)
    (hR : ∀ᶠ n : ℕ in atTop, 2 ≤ R n)
    (hscale :
      Tendsto
        (fun n : ℕ =>
          (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
            (Nseq n : ℝ))
        atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      2 * R n ^ (2 * Fintype.card (CFZFormIndex k)) ≤
        Nseq n := by
  have hfullPos :
      0 < Fintype.card (CFZFormIndex k) := by
    apply Fintype.card_pos_iff.mpr
    exact
      ⟨⟨⟨0, by omega⟩, fun _ => false⟩⟩
  have hclose :
      ∀ᶠ n : ℕ in atTop,
        dist
          ((R n : ℝ) ^
              cfzCanonicalCyclicBoundaryExponent k /
            (Nseq n : ℝ))
          0 < 1 :=
    (Metric.tendsto_nhds.mp hscale) 1 zero_lt_one
  filter_upwards [hR, hclose] with n hRn hcloseN
  have hNposNat : 0 < Nseq n :=
    Nat.pos_of_ne_zero (hN n)
  have hNpos : (0 : ℝ) < Nseq n := by
    exact_mod_cast hNposNat
  have hquotNonneg :
      0 ≤
        (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
          (Nseq n : ℝ) :=
    div_nonneg (by positivity) hNpos.le
  have hquotLt :
      (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
          (Nseq n : ℝ) < 1 := by
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg hquotNonneg] using hcloseN
  rw [div_lt_one hNpos] at hquotLt
  have hpowLt :
      R n ^ cfzCanonicalCyclicBoundaryExponent k <
        Nseq n := by
    exact_mod_cast hquotLt
  have hextra : 1 ≤ 3 * Fintype.card (CFZFormIndex k) := by
    omega
  have hpowExtra :
      2 ≤ R n ^ (3 * Fintype.card (CFZFormIndex k)) := by
    calc
      2 ≤ R n := hRn
      _ = R n ^ 1 := by simp
      _ ≤ R n ^ (3 * Fintype.card (CFZFormIndex k)) :=
        Nat.pow_le_pow_right (by omega) hextra
  have hboxPower :
      2 * R n ^ (2 * Fintype.card (CFZFormIndex k)) ≤
        R n ^ cfzCanonicalCyclicBoundaryExponent k := by
    calc
      2 * R n ^ (2 * Fintype.card (CFZFormIndex k)) ≤
          R n ^ (3 * Fintype.card (CFZFormIndex k)) *
            R n ^ (2 * Fintype.card (CFZFormIndex k)) :=
        Nat.mul_le_mul_right _ hpowExtra
      _ = R n ^ cfzCanonicalCyclicBoundaryExponent k := by
        rw [← pow_add]
        unfold cfzCanonicalCyclicBoundaryExponent
        congr 1
        omega
  exact hboxPower.trans hpowLt.le
