-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.tendsto_sieveLevel_cfzCanonicalCyclicBoundaryPower_div
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:49:23.383867+00:00
-- url     : https://prove2.me/submissions/fe7a39f3-3502-47d7-899d-362a0d7cde1a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
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

section




/-!
# Quantitative parameters for the Green--Tao argument

This file fixes deliberately coarse constants for the sieve and
transference layers.  The important feature is their dependency order:
`maxAPForms`, `sieveExponent`, and `primeScale` depend only on the
progression length (and the fixed smooth-cutoff normalizer), while
`sieveLevel` is the first parameter that depends on the cyclic modulus.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Real













theorem maxAPForms_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < maxAPForms k := by
  exact Nat.mul_pos (by omega) (pow_pos (by norm_num) _)































end Wikipedia.SzemeredisTheorem

end

section



/-!
# The Green--Tao cyclic-majorant scale

This file verifies that the concrete sieve level chosen in
`GreenTao.Parameters` has enough power saving for the complete cyclic
boundary estimate.  The calculation is independent of all Fourier and
residue parameters.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Real Topology

/-- The ambient CFZ family has exactly the coarse cardinality used when the
Green--Tao sieve exponent was chosen. -/
theorem card_CFZFormIndex_eq_maxAPForms (k : ℕ) :
    Fintype.card (CFZFormIndex k) = maxAPForms k := by
  simp [CFZFormIndex, DeletedCube, maxAPForms]

/-- The boundary power uses exactly one twentieth of the ambient modulus
power available in the chosen sieve scale. -/
theorem sieveExponent_mul_cfzCanonicalCyclicBoundaryExponent
    {k : ℕ} (hk : 3 ≤ k) :
    sieveExponent k *
        (cfzCanonicalCyclicBoundaryExponent k : ℝ) =
      1 / 20 := by
  have hforms : (maxAPForms k : ℝ) ≠ 0 := by
    exact_mod_cast (maxAPForms_pos hk).ne'
  rw [sieveExponent, cfzCanonicalCyclicBoundaryExponent,
    card_CFZFormIndex_eq_maxAPForms]
  push_cast
  field_simp [hforms]
  ring







end Wikipedia.SzemeredisTheorem

end
/-!
# The Green--Tao cyclic-majorant scale

This file verifies that the concrete sieve level chosen in
`GreenTao.Parameters` has enough power saving for the complete cyclic
boundary estimate.  The calculation is independent of all Fourier and
residue parameters.
-/
open Wikipedia.SzemeredisTheorem
open Filter Real Topology

open Wikipedia.SzemeredisTheorem in
/-- The concrete Green--Tao sieve level has more than enough power saving
for the complete cyclic-to-Euler boundary. -/
theorem solution
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto
      (fun N : ℕ =>
        (sieveLevel k N : ℝ) ^
            cfzCanonicalCyclicBoundaryExponent k /
          (N : ℝ))
      atTop (𝓝 0) := by
  let A := cfzCanonicalCyclicBoundaryExponent k
  have hgap :
      0 < 1 - sieveExponent k * (A : ℝ) := by
    rw [show sieveExponent k * (A : ℝ) = 1 / 20 by
      exact sieveExponent_mul_cfzCanonicalCyclicBoundaryExponent hk]
    norm_num
  have hmodel :
      Tendsto
        (fun N : ℕ =>
          (N : ℝ) ^ (sieveExponent k * (A : ℝ) - 1))
        atTop (𝓝 0) := by
    have h :=
      (tendsto_rpow_neg_atTop hgap).comp
        tendsto_natCast_atTop_atTop
    convert h using 1
    funext N
    congr 1
    ring
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N =>
      div_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast hN
    have hfloor :
        (sieveLevel k N : ℝ) ≤
          (N : ℝ) ^ sieveExponent k := by
      exact Nat.floor_le
        (Real.rpow_nonneg hNpos.le _)
    have hpow :
        (sieveLevel k N : ℝ) ^ A ≤
          ((N : ℝ) ^ sieveExponent k) ^ A :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor A
    calc
      (sieveLevel k N : ℝ) ^ A / (N : ℝ) ≤
          ((N : ℝ) ^ sieveExponent k) ^ A /
            (N : ℝ) :=
        div_le_div_of_nonneg_right hpow hNpos.le
      _ =
          (N : ℝ) ^
            (sieveExponent k * (A : ℝ) - 1) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul hNpos.le,
          div_eq_mul_inv, ← Real.rpow_neg_one,
          ← Real.rpow_add hNpos]
        congr 1
  · exact hmodel
