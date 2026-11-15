-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.tendsto_normalizedSmallPrimeZetaCorrection_sieveLevel_fixed
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:50:06.215657+00:00
-- url     : https://prove2.me/submissions/9e357ed3-fcb1-46d4-953c-8189cfd57bc1

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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierEulerNormalization
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrectionLimit
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
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Theorems.Thm_Wikipedia_SzemeredisTheorem_tendsto_cutoffPhaseMagnitudeBound_sqrt_log_fixed
import Theorems.Thm_Wikipedia_SzemeredisTheorem_tendsto_normalizedSmallPrimeZetaCorrection_of_joint_scale

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

theorem sieveExponent_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < sieveExponent k := by
  rw [sieveExponent]
  apply inv_pos.mpr
  exact_mod_cast
    Nat.mul_pos (by norm_num) (maxAPForms_pos hk)





















/-- The sieve level tends to infinity for every progression length in the
nontrivial range. -/
theorem tendsto_sieveLevel_atTop {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (sieveLevel k) atTop atTop := by
  change Tendsto
    (fun N : ℕ ↦ ⌊(N : ℝ) ^ sieveExponent k⌋₊)
    atTop atTop
  simpa [Function.comp_def] using
    tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (sieveExponent_pos hk)).comp
        tendsto_natCast_atTop_atTop)



theorem eventually_two_le_sieveLevel {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ sieveLevel k N :=
  (tendsto_sieveLevel_atTop hk).eventually
    (eventually_ge_atTop 2)



end Wikipedia.SzemeredisTheorem

end

section




/-!
# Fixed-primorial Fourier schedules

The Green--Tao parameter order first chooses a large primorial cutoff `w`
and then lets the cyclic modulus tend to infinity.  This file records the
analytic consequences of that order for the concrete sieve level
`sieveLevel k N`.

For fixed `w`, the conventional Fourier radius

`T N = sqrt (log (sieveLevel k N))`

is already small enough for the finite small-prime correction.  Indeed its
quadratic error scale is `O_w(1 / log (sieveLevel k N))`.  Thus no smaller
sub-box is needed.

The large-prime correction has a different quantifier order.  For a fixed
cutoff it need not converge to one as the carry block varies.  What the
uniform prime-square estimate gives, and what the Green--Tao argument
actually uses, is:

`∀ ε > 0, ∃ w₀, ∀ carry blocks with w ≥ w₀, ‖largeCorrection - 1‖ < ε`.

The results below record the fixed-`w` limits and this uniform tail
statement side by side, together with a completed-correction wrapper that
isolates the exact remaining large-prime hypothesis.  They deliberately do
not assert a false fixed-`w` limit for the actual carry correction.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-! ## The fixed-primorial phase scale -/





/-- The exact quadratic scale used by
`tendsto_normalizedSmallPrimeZetaCorrection_of_joint_scale` vanishes for a
fixed primorial and the full `sqrt (log R)` Fourier box. -/
theorem tendsto_fixedPrimorialPhaseScale_sqrt_log
    (R : ℕ → ℕ) (w : ℕ)
    (hR : Tendsto R atTop atTop) :
    Tendsto
      (fun n =>
        (((w + 1 : ℕ) : ℝ) *
          cutoffPhaseMagnitudeBound
            (R n) w (Real.sqrt (Real.log (R n))) ^ 2))
      atTop (𝓝 0) := by
  have hphase :=
    tendsto_cutoffPhaseMagnitudeBound_sqrt_log_fixed R w hR
  simpa using
    (tendsto_const_nhds.mul (hphase.pow 2) :
      Tendsto
        (fun n =>
          (((w + 1 : ℕ) : ℝ) *
            cutoffPhaseMagnitudeBound
              (R n) w (Real.sqrt (Real.log (R n))) ^ 2))
        atTop (𝓝 (((w + 1 : ℕ) : ℝ) * 0 ^ 2)))

/-- Specialization of the preceding phase calculation to the standard
Green--Tao sieve level. -/
theorem tendsto_fixedPrimorialSievePhaseScale_sqrt_log
    {k : ℕ} (hk : 3 ≤ k) (w : ℕ) :
    Tendsto
      (fun N =>
        (((w + 1 : ℕ) : ℝ) *
          cutoffPhaseMagnitudeBound
            (sieveLevel k N) w
              (Real.sqrt (Real.log (sieveLevel k N))) ^ 2))
      atTop (𝓝 0) :=
  tendsto_fixedPrimorialPhaseScale_sqrt_log
    (sieveLevel k) w (tendsto_sieveLevel_atTop hk)

/-! ## Fixed-primorial finite correction limits -/









/-! ## The honest large-prime tail bridge -/



end Wikipedia.SzemeredisTheorem

end
/-!
# Fixed-primorial Fourier schedules

The Green--Tao parameter order first chooses a large primorial cutoff `w`
and then lets the cyclic modulus tend to infinity.  This file records the
analytic consequences of that order for the concrete sieve level
`sieveLevel k N`.

For fixed `w`, the conventional Fourier radius

`T N = sqrt (log (sieveLevel k N))`

is already small enough for the finite small-prime correction.  Indeed its
quadratic error scale is `O_w(1 / log (sieveLevel k N))`.  Thus no smaller
sub-box is needed.

The large-prime correction has a different quantifier order.  For a fixed
cutoff it need not converge to one as the carry block varies.  What the
uniform prime-square estimate gives, and what the Green--Tao argument
actually uses, is:

`∀ ε > 0, ∃ w₀, ∀ carry blocks with w ≥ w₀, ‖largeCorrection - 1‖ < ε`.

The results below record the fixed-`w` limits and this uniform tail
statement side by side, together with a completed-correction wrapper that
isolates the exact remaining large-prime hypothesis.  They deliberately do
not assert a false fixed-`w` limit for the actual carry correction.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology
/-! ## The fixed-primorial phase scale -/
/-! ## Fixed-primorial finite correction limits -/

open Wikipedia.SzemeredisTheorem in
/-- The normalized correction from the finitely many primes dividing the
fixed primorial tends uniformly to one throughout the conventional growing
Fourier box. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {k w : ℕ} (hk : 3 ≤ k) (hw : 2 ≤ w)
    (t u : ℕ → κ → ℝ)
    (ht :
      ∀ᶠ N in atTop, ∀ q,
        |t N q| ≤
          Real.sqrt (Real.log (sieveLevel k N)))
    (hu :
      ∀ᶠ N in atTop, ∀ q,
        |u N q| ≤
          Real.sqrt (Real.log (sieveLevel k N))) :
    Tendsto
      (fun N =>
        normalizedSmallPrimeZetaCorrection
          (sieveLevel k N) w (t N) (u N))
      atTop (𝓝 1) := by
  apply
    tendsto_normalizedSmallPrimeZetaCorrection_of_joint_scale
      (sieveLevel k) (fun _ => w)
      (fun N => Real.sqrt (Real.log (sieveLevel k N)))
      t u
  · exact eventually_two_le_sieveLevel hk
  · exact Filter.Eventually.of_forall fun _ => hw
  · exact Filter.Eventually.of_forall fun _ =>
      Real.sqrt_nonneg _
  · exact ht
  · exact hu
  · simpa using
      tendsto_fixedPrimorialSievePhaseScale_sqrt_log hk w
