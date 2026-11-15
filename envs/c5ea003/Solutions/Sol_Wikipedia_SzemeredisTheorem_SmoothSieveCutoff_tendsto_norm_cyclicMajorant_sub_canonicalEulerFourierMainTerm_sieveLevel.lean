-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.tendsto_norm_cyclicMajorant_sub_canonicalEulerFourierMainTerm_sieveLevel
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:17:43.892036+00:00
-- url     : https://prove2.me/submissions/c5493c3c-08be-4f6b-9c2e-71b532555678

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_tendsto_norm_cyclicMajorant_sub_eulerFourierMainTerm_of_power_schedule_and_fit
import Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_two_mul_cfzDivisorBox_le_of_boundaryPower_tendsto_zero
import Theorems.Thm_Wikipedia_SzemeredisTheorem_tendsto_sieveLevel_cfzCanonicalCyclicBoundaryPower_div

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







end Wikipedia.SzemeredisTheorem

end

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

section





/-!
# Summed canonical cyclic-to-Euler boundary

The canonical carry partition compares the cyclic paired-divisibility
density with a divisor-independent affine Euler model.  Its pointwise error
is proportional to the paired-divisor LCM divided by the cyclic modulus.
This file sums that estimate over every divisor family selected by a
Boolean CFZ exponent, restores the Selberg normalization, and records a
joint power-scale limit.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped ArithmeticFunction.Moebius BigOperators













/-! ## Selberg-scaled canonical main terms -/















/-! ## A single polynomial joint scale -/





















/-- Clean power-schedule endpoint against the exact complex Fourier main
term. -/
theorem
    SmoothSieveCutoff.tendsto_norm_cyclicMajorant_sub_eulerFourierMainTerm_of_power_schedule
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (R Nseq wseq bseq : ℕ → ℕ)
    (hN : ∀ n, Nseq n ≠ 0)
    (hR : ∀ᶠ n : ℕ in atTop, 2 ≤ R n)
    (hb : ∀ᶠ n : ℕ in atTop, 0 < bseq n)
    (hscale :
      Tendsto
        (fun n : ℕ =>
          (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
            (Nseq n : ℝ))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        letI : NeZero (Nseq n) := ⟨hN n⟩
        ‖(mean
              (linearFormsProduct k (Nseq n)
                (χ.cyclicMajorant
                  (R n) (primorial (wseq n)) (bseq n)) e) : ℂ) -
            χ.selectedCFZCanonicalEulerFourierMainTerm
              (N := Nseq n) (R n)
              (primorial (wseq n)) (bseq n) e‖)
      atTop (𝓝 0) := by
  have hfit :=
    eventually_two_mul_cfzDivisorBox_le_of_boundaryPower_tendsto_zero
      hk R Nseq hN hR hscale
  exact
    χ.tendsto_norm_cyclicMajorant_sub_eulerFourierMainTerm_of_power_schedule_and_fit
      hk e R Nseq wseq bseq hN hR hb hfit hscale

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







/-- Shifted form matching the nonzero cyclic modulus `M + 1`. -/
theorem tendsto_sieveLevel_cfzCanonicalCyclicBoundaryPower_div_succ
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto
      (fun M : ℕ =>
        (sieveLevel k (M + 1) : ℝ) ^
            cfzCanonicalCyclicBoundaryExponent k /
          (M + 1 : ℕ))
      atTop (𝓝 0) := by
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    (tendsto_sieveLevel_cfzCanonicalCyclicBoundaryPower_div hk).comp
      (tendsto_add_atTop_nat 1)



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

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- The cyclic boundary vanishes for the exact Green--Tao sieve level and
every fixed primorial/residue pair. -/
theorem
    solution
    {k w b : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 3 ≤ k)
    (hb : 0 < b)
    (e : LinearFormsExponent k) :
    Tendsto
      (fun M : ℕ =>
        letI : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
        ‖(mean
              (linearFormsProduct k (M + 1)
                (χ.cyclicMajorant
                  (sieveLevel k (M + 1))
                  (primorial w) b) e) : ℂ) -
            χ.selectedCFZCanonicalEulerFourierMainTerm
              (N := M + 1) (sieveLevel k (M + 1))
              (primorial w) b e‖)
      atTop (𝓝 0) := by
  have hRtop :
      Tendsto (fun M : ℕ => sieveLevel k (M + 1))
        atTop atTop :=
    (tendsto_sieveLevel_atTop hk).comp
      (tendsto_add_atTop_nat 1)
  have hR :
      ∀ᶠ M : ℕ in atTop,
        2 ≤ sieveLevel k (M + 1) :=
    hRtop (eventually_ge_atTop 2)
  simpa using
    χ.tendsto_norm_cyclicMajorant_sub_eulerFourierMainTerm_of_power_schedule
      (show 2 ≤ k by omega) e
      (fun M => sieveLevel k (M + 1))
      (fun M => M + 1)
      (fun _M => w)
      (fun _M => b)
      (fun M => Nat.succ_ne_zero M)
      hR
      (Filter.Eventually.of_forall fun _M => hb)
      (tendsto_sieveLevel_cfzCanonicalCyclicBoundaryPower_div_succ hk)
