-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.tendsto_abs_cyclicMajorant_sub_eulerMainTerm_of_power_schedule_and_fit
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:15:03.953475+00:00
-- url     : https://prove2.me/submissions/ab63c210-e1fa-4cf4-b14e-a5e1c9a41b2f

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_abs_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_le_power

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

section




/-!
# Large-prime geometry for W-tricked affine systems

The integer exceptional-prime bound of a system scales with `W` after
replacing every form `ψ` by `W * ψ + b`.  That bound is therefore the wrong
interface for the large primes in the W-tricked Euler product.  Modulo a
prime `p ∤ W`, multiplication by `W` is a unit.  Consequently:

* a nonzero coefficient modulo `p` stays nonzero;
* every nonzero two-by-two coefficient minor stays nonzero, since the minor
  is multiplied by `W²`;
* affine constants play no role in either assertion and may vary from form
  to form.

This file packages that observation as direct modular good-prime predicates,
derives the exact one- and two-form densities without applying an exceptional
bound to the transformed integer system, and rebuilds the complex
paired-Fourier local-factor estimates from those modular hypotheses.

The final results apply uniformly to every subtype `SelectedCFZFormIndex e`.
Their exceptional cutoff depends only on the ambient CFZ parameter `k`.
The W-trick contributes only the natural hypothesis `p ∤ W`; neither the
size of `W` nor any (possibly carry-dependent) affine constant enters the
cutoff.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Modular one-form geometry -/









/-! ## Scaling identities and W-trick preservation -/

















/-! ## Exact one- and two-form densities -/









/-! ## Complex first-order expansion from modular geometry -/





/-! ## Stable complex and paired-Fourier ratios -/







/-! ## Direct comparison with the zeta Euler model -/





/-! ## Uniform selected-CFZ specialization -/

/-- The number of forms selected by a Boolean exponent is at most the
number of forms in the ambient CFZ system. -/
theorem card_selectedCFZFormIndex_le
    {k : ℕ} (e : LinearFormsExponent k) :
    Fintype.card (SelectedCFZFormIndex e) ≤
      Fintype.card (CFZFormIndex k) := by
  exact Fintype.card_subtype_le _























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
/-- Joint asymptotic vanishing of the complete canonical cyclic boundary.
The power schedule is uniform in the Boolean-selected subfamily; the global
fit condition is likewise stated using the ambient CFZ family. -/
theorem
    solution
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (R Nseq wseq bseq : ℕ → ℕ)
    (hN : ∀ n, Nseq n ≠ 0)
    (hR : ∀ᶠ n : ℕ in atTop, 2 ≤ R n)
    (hb : ∀ᶠ n : ℕ in atTop, 0 < bseq n)
    (hfit :
      ∀ᶠ n : ℕ in atTop,
        2 * R n ^ (2 * Fintype.card (CFZFormIndex k)) ≤
          Nseq n)
    (hscale :
      Tendsto
        (fun n : ℕ =>
          (R n : ℝ) ^ cfzCanonicalCyclicBoundaryExponent k /
            (Nseq n : ℝ))
        atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        letI : NeZero (Nseq n) := ⟨hN n⟩
        |mean
              (linearFormsProduct k (Nseq n)
                (χ.cyclicMajorant
                  (R n) (primorial (wseq n)) (bseq n)) e) -
            χ.selectedCFZCanonicalEulerMainTerm
              (N := Nseq n) (R n)
              (primorial (wseq n)) (bseq n) e|)
      atTop (𝓝 0) := by
  let C :=
    χ.selectedCFZCanonicalScaledCyclicBoundaryConstant e
  have hupper :
      Tendsto
        (fun n : ℕ =>
          C *
            ((R n : ℝ) ^
                cfzCanonicalCyclicBoundaryExponent k /
              (Nseq n : ℝ)))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hscale)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => by
      let : NeZero (Nseq n) := ⟨hN n⟩
      exact abs_nonneg _
  · filter_upwards [hR, hb, hfit] with n hRn hbn hfitn
    let : NeZero (Nseq n) := ⟨hN n⟩
    have hcard :
        Fintype.card (SelectedCFZFormIndex e) ≤
          Fintype.card (CFZFormIndex k) :=
      card_selectedCFZFormIndex_le e
    have hpow :
        R n ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤
          R n ^ (2 * Fintype.card (CFZFormIndex k)) :=
      Nat.pow_le_pow_right (by omega)
        (Nat.mul_le_mul_left 2 hcard)
    have hselectedFit :
        2 * R n ^ (2 * Fintype.card (SelectedCFZFormIndex e)) ≤
          Nseq n :=
      (Nat.mul_le_mul_left 2 hpow).trans hfitn
    exact
      χ.abs_cyclicMajorant_sub_canonicalEulerMainTerm_primorial_le_power
        hk hRn hbn e hselectedFit (w := wseq n)
  · simpa only [C, mul_div_assoc] using hupper
