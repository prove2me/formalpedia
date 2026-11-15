-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.norm_cfzCanonicalCarryCompleteEulerIntegrand_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:01:46.126108+00:00
-- url     : https://prove2.me/submissions/a857e8d9-c5f5-4ea6-89fc-6ffc7d17a517

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorIntegralCancellation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorRankinTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletionTail
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
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
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_pairedEnvelope_mul_selectedCFZCanonicalCarryCompletePrimeSupportSeries_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_cfzCanonicalCarryCellDensity_eq_one

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section







/-!
# Congruence averages on finite boxes

This file supplies the elementary finite-arithmetic layer used after expanding
the Selberg sieve weight.  A finite family of divisor moduli is combined by an
LCM, while a function depending only on coordinatewise residues is averaged
exactly over boxes whose side lengths are multiples of that LCM.

There are two equivalent box models:

* `natBox side` is the literal finset of natural-valued points satisfying
  `x i < side i`;
* `FiniteBox side` is the finite type `∀ i, Fin (side i)`.

The second model makes quotient--remainder reindexing transparent, and
`boxSum_eq_sum_natBox` transports its sums back to the literal finset.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## LCM bounds -/









/-! ## Finite boxes -/















/-- `boxSum` is the usual sum over the literal finset `natBox`. -/
theorem boxSum_eq_sum_natBox {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (side : ι → ℕ) (F : (ι → ℕ) → A) :
    boxSum side F = ∑ x ∈ natBox side, F x := by
  rw [← Finset.sum_coe_sort]
  exact Fintype.sum_equiv (finiteBoxEquivNatBox side)
    (fun x : FiniteBox side ↦ F (fun i ↦ x i))
    (fun x : ↥(natBox side) ↦ F x)
    (fun _ ↦ rfl)

/-! ## Coordinatewise periodicity and exact box sums -/



























/-! ## Exact means -/









/-! ## Trimming and explicit boundary loss -/































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
# Polylogarithmic growth of the canonical Rankin mass

The canonical coordinatewise-truncation estimate leaves a sharp arithmetic
Rankin mass.  This file proves that mass grows only polylogarithmically in
the selected CFZ, primorial, and reduced-residue regime.

There are two contributions.

* In the coordinatewise-truncated fibers, every divisor phase has norm at
  most one.  Every nonempty good-prime support costs at least `1 / p`, while
  a support at a prime dividing the primorial has zero density.  The
  truncated contribution is therefore bounded by the existing harmonic-LCM
  Euler majorant.
* The unrestricted Rpow coefficient mass factors over primes.  Its empty
  local support contributes one.  The total coefficient weight of all
  supports is at most `4 ^ m`, where `m` is the number of selected forms,
  and every nonempty support again costs `1 / p`.

The canonical carry-cell densities are nonnegative and sum exactly to one,
so these bounds are uniform in the carry vector.  Finally the existing
Selberg-scale estimate supplies one additional logarithm per selected form.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped BigOperators

/-! ## The canonical carry cells form a probability partition -/

/-- A canonical carry-cell density is its cardinality divided by the
cardinality of the ambient natural box. -/
theorem cfzCanonicalCarryCellDensity_eq_card_div
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) :
    cfzCanonicalCarryCellDensity (N := N) forms carry =
      ((cfzCanonicalCarryCell (N := N) forms carry).card : ℝ) /
        ∏ _v : CFZVariable k, (N : ℝ) := by
  unfold cfzCanonicalCarryCellDensity boxMean
  rw [boxSum_eq_sum_natBox]
  unfold cfzCanonicalCarryCell cfzCanonicalCarryIndicator
  simp

theorem cfzCanonicalCarryCellDensity_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) :
    0 ≤ cfzCanonicalCarryCellDensity (N := N) forms carry := by
  rw [cfzCanonicalCarryCellDensity_eq_card_div]
  positivity



/-! ## Divisor phases and fixed-carry support densities -/











/-! ## The coordinatewise-truncated part -/





/-! ## The unrestricted Rpow part -/

















/-! ## Fixed-family and carry-averaged mass bounds -/







/-! ## Primorial polylogarithmic bounds -/



















end Wikipedia.SzemeredisTheorem

end
/-!
# Polylogarithmic control of the canonical Euler-completion tail

The complete-support majorant has local factor

`1 + 3m p^(-1-1/log R) + 4^m p^(-2)`,

where `m` is the number of selected CFZ forms.  We compare its two
nonconstant pieces with the Euler products for
`ζ(1 + 1 / log R)` and `ζ(2)`.  The elementary bound
`‖ζ(1 + 1 / log R)‖ ≤ 1 + log R` then gives an explicit
polylogarithmic bound for the whole infinite support mass, and hence for
the genuinely missing completion tail.
-/
open Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Topology
open scoped BigOperators
/-! ## A two-factor Euler comparison -/
/-! ## The infinite support mass -/
/-! ## Pointwise and complementary-box bounds -/
/-! ## The completed Euler model on the complementary box -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Pointwise bound for the completed carry-weighted Euler integrand.
The exact probability normalization of carry-cell densities removes all
dependence on `N`. -/
theorem solution
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    ‖χ.cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) tu‖ ≤
      selectedCFZCanonicalCompleteSupportMass e R *
        χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
  classical
  unfold SmoothSieveCutoff.cfzCanonicalCarryCompleteEulerIntegrand
    cfzCanonicalCarryCompleteFourierAverage
  rw [Finset.mul_sum]
  calc
    ‖∑ carry ∈ cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k,
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          ((cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry : ℂ) *
            cfzCanonicalCarryCompletePrimeSupportSeries
              N (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1)
              carry tu.1 tu.2)‖ ≤
        ∑ carry ∈ cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k,
          ‖pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            ((cfzCanonicalCarryCellDensity
                (N := N)
                (fun q : SelectedCFZFormIndex e => q.1)
                carry : ℂ) *
              cfzCanonicalCarryCompletePrimeSupportSeries
                N (primorial w) b R
                (fun q : SelectedCFZFormIndex e => q.1)
                carry tu.1 tu.2)‖ :=
      norm_sum_le _ _
    _ ≤
        ∑ carry ∈ cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k,
          cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry *
            (selectedCFZCanonicalCompleteSupportMass e R *
              χ.selectedCFZPairedFourierAbsoluteDensity e tu) := by
      apply Finset.sum_le_sum
      intro carry hcarry
      have hdensity :
          0 ≤
            cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry :=
        cfzCanonicalCarryCellDensity_nonneg
          (N := N)
          (fun q : SelectedCFZFormIndex e => q.1)
          carry
      have hcarryBound :=
        χ.norm_pairedEnvelope_mul_selectedCFZCanonicalCarryCompletePrimeSupportSeries_le
          (N := N) hk hbound hwb e carry hR tu
      rw [show
          pairedCutoffFourierEnvelope χ tu.1 tu.2 *
              ((cfzCanonicalCarryCellDensity
                  (N := N)
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry : ℂ) *
                cfzCanonicalCarryCompletePrimeSupportSeries
                  N (primorial w) b R
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry tu.1 tu.2) =
            (cfzCanonicalCarryCellDensity
                (N := N)
                (fun q : SelectedCFZFormIndex e => q.1)
                carry : ℂ) *
              (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                cfzCanonicalCarryCompletePrimeSupportSeries
                  N (primorial w) b R
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry tu.1 tu.2) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hdensity]
      exact mul_le_mul_of_nonneg_left hcarryBound hdensity
    _ =
        selectedCFZCanonicalCompleteSupportMass e R *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
      rw [← Finset.sum_mul,
        sum_cfzCanonicalCarryCellDensity_eq_one]
      simp
