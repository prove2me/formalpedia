-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.integral_cfzCanonicalCarryTruncationDiscrepancy_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:31:12.255279+00:00
-- url     : https://prove2.me/submissions/c9cd5da1-8b88-4746-a3ee-c8efa9f05d97

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integral_transformedDivisorFamilySide_eq_prod
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_smoothDivisorFamilyCoefficient_eq_zero_of_not_mem
import Theorems.Thm_Wikipedia_SzemeredisTheorem_fixedFamilyPairedPrimeStateDivisorFamily_assignmentOf_eq
import Theorems.Thm_Wikipedia_SzemeredisTheorem_integrable_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient
import Theorems.Thm_Wikipedia_SzemeredisTheorem_integral_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient_eq_sum_states

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Fourier inversion for the smooth sieve cutoff

This file supplies the analytic transform used in the Goldston--Yıldırım
calculation.  For a smooth sieve cutoff `χ`, put

`g(x) = exp(x) χ(x)`.

We regard `g` as complex-valued and use Mathlib's analyst normalization

`𝓕 g(t) = ∫ x, exp(-2 π i x t) g(x)`.

The function `g` is smooth and compactly supported, hence is a Schwartz
function.  Its Fourier transform is therefore again Schwartz and in
particular integrable.  Fourier inversion gives

`χ(x) = ∫ t, 𝓕 g(t) exp(-x + 2 π i t x)`.

At `x = log d / log R`, the last exponential is multiplicative in `d`.
The final results interchange this integral with the finite divisor sums
that occur in the truncated divisor sum.
-/

namespace Wikipedia.SzemeredisTheorem

open Function MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators FourierTransform
  ContDiff SchwartzMap

namespace SmoothSieveCutoff





















/-- The cutoff transform is integrable, as needed for pointwise Fourier
inversion. -/
theorem cutoffFourierTransform_integrable (χ : SmoothSieveCutoff) :
    Integrable χ.cutoffFourierTransform := by
  change Integrable (χ.cutoffFourierSchwartz : ℝ → ℂ)
  exact χ.cutoffFourierSchwartz.integrable









@[simp]
theorem norm_inverseFourierCharacter (x t : ℝ) :
    ‖inverseFourierCharacter x t‖ = 1 := by
  rw [inverseFourierCharacter, Complex.norm_exp]
  simp

theorem continuous_inverseFourierCharacter (x : ℝ) :
    Continuous (inverseFourierCharacter x) := by
  unfold inverseFourierCharacter
  fun_prop

/-- Multiplying the integrable Fourier transform by an inverse Fourier
character preserves integrability. -/
theorem integrable_cutoffFourierTransform_mul_inverseFourierCharacter
    (χ : SmoothSieveCutoff) (x : ℝ) :
    Integrable
      (fun t : ℝ ↦
        χ.cutoffFourierTransform t * inverseFourierCharacter x t) := by
  refine χ.cutoffFourierTransform_integrable.mul_bdd
    (c := 1) ?_ ?_
  · exact (continuous_inverseFourierCharacter x).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t ↦ by
      rw [norm_inverseFourierCharacter]





/-- The cutoff phase is the inverse Fourier character times the real
exponential `exp(-x)`. -/
theorem cutoffMultiplicativePhase_eq
    (x t : ℝ) :
    cutoffMultiplicativePhase x t =
      (Real.exp (-x) : ℂ) * inverseFourierCharacter x t := by
  simp only [cutoffMultiplicativePhase, inverseFourierCharacter,
    Complex.exp_add, Complex.ofReal_neg, Complex.ofReal_exp]



/-- The integrand in the cutoff inversion formula is integrable. -/
theorem integrable_cutoffFourierTransform_mul_cutoffMultiplicativePhase
    (χ : SmoothSieveCutoff) (x : ℝ) :
    Integrable
      (fun t : ℝ ↦
        χ.cutoffFourierTransform t *
          cutoffMultiplicativePhase x t) := by
  have h :=
    (χ.integrable_cutoffFourierTransform_mul_inverseFourierCharacter x).mul_const
      (Real.exp (-x) : ℂ)
  convert h using 1
  funext t
  rw [cutoffMultiplicativePhase_eq]
  ring









/-- The integral occurring in a transformed divisor summand is integrable. -/
theorem integrable_transformedSmoothDivisorSummand
    (χ : SmoothSieveCutoff) (R d : ℕ) :
    Integrable
      (fun t : ℝ ↦
        (ArithmeticFunction.moebius d : ℂ) *
          χ.cutoffFourierTransform t *
            divisorMultiplicativePhase R d t) := by
  have h :=
    (χ.integrable_cutoffFourierTransform_mul_cutoffMultiplicativePhase
      (Real.log d / Real.log R)).const_mul
      (ArithmeticFunction.moebius d : ℂ)
  simpa only [divisorMultiplicativePhase, mul_assoc] using h





end SmoothSieveCutoff

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
# Multivariate Fourier rewrite of the divisor expansion

The finite Selberg-square expansion has two smooth divisor coefficients for
each form.  Fourier inversion turns those `2 * card κ` coefficients into a
single integral over two copies of `κ → ℝ`.

This file proves that rewrite exactly.  All sum/integral interchanges are
finite, while absolute integrability follows coordinatewise from the
Schwartz transform.  The arithmetic divisibility density is left as an
arbitrary real coefficient, ready for the Euler-product comparison.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff



/-- The coordinatewise transformed divisor family is absolutely
integrable. -/
theorem integrable_transformedDivisorFamilySide
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (d : κ → ℕ) :
    Integrable (χ.transformedDivisorFamilySide R d :
      (κ → ℝ) → ℂ) := by
  rw [MeasureTheory.volume_pi]
  exact Integrable.fintype_prod fun q =>
    χ.integrable_transformedSmoothDivisorSummand R (d q)





/-- Absolute integrability of one full paired-family integrand. -/
theorem integrable_transformedPairedDivisorFamily
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ) :
    Integrable
      (χ.transformedPairedDivisorFamily R z)
      (volume.prod volume) :=
  (χ.integrable_transformedDivisorFamilySide R
      (fun q => (z q).1)).mul_prod
    (χ.integrable_transformedDivisorFamilySide R
      (fun q => (z q).2))

/-- Product-space integral of a paired divisor family. -/
theorem integral_transformedPairedDivisorFamily_eq
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        χ.transformedPairedDivisorFamily R z tu
        ∂(volume.prod volume)) =
      (∏ q,
          (smoothDivisorSummand
            χ.toFun R (z q).1 : ℂ)) *
        ∏ q,
          (smoothDivisorSummand
            χ.toFun R (z q).2 : ℂ) := by
  unfold transformedPairedDivisorFamily
  rw [integral_prod_mul,
    χ.integral_transformedDivisorFamilySide_eq_prod
      R (fun q => (z q).1),
    χ.integral_transformedDivisorFamilySide_eq_prod
      R (fun q => (z q).2)]

/-- Exact Fourier integral for the smooth coefficient of one paired divisor
family. -/
theorem smoothDivisorFamilyCoefficient_eq_integral
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ) :
    (smoothDivisorFamilyCoefficient χ.toFun R z : ℂ) =
      ∫ tu : (κ → ℝ) × (κ → ℝ),
        χ.transformedPairedDivisorFamily R z tu
        ∂(volume.prod volume) := by
  rw [χ.integral_transformedPairedDivisorFamily_eq R z]
  unfold smoothDivisorFamilyCoefficient
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl









end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end

section






/-!
# Squarefree paired divisors and finite-family local factors

The Selberg expansion only receives a contribution from squarefree divisor
choices: a nonzero Möbius coefficient forces each of the two divisors attached
to every form to be squarefree.  Consequently all local least common multiples,
and their global least common multiple, are squarefree.  The canonical
prime-power CRT from `PairedDivisibilityCRT` therefore has exponent one at
every prime.

This file records that reduction exactly.  It also packages the local
intersection density of an arbitrary finite subfamily of affine forms.  The
empty, singleton, and two-element cases reduce to the exact APIs in
`LocalFactors`; the full avoidance factor is their finite
inclusion--exclusion sum.  Higher intersections require an additional
arithmetic input, so the final interface exposes that input as a hypothesis
rather than asserting an unavailable estimate.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Squarefree divisor choices -/

















/-! ## Exact prime support and the squarefree indicator product -/



@[simp]
theorem mem_pairedPrimeSupport
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) (p : ℕ) (q : κ) :
    q ∈ pairedPrimeSupport z p ↔ p ∣ pairedLocalModulus z q := by
  simp [pairedPrimeSupport]







/-! ## Arbitrary finite-family intersection densities -/

























/-! ## Exact arbitrary-family local factor formula -/









/-! ## Localization of the canonical CRT factors -/



















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
# A finite Euler majorant for the carry harmonic LCM mass

The divisor cutoff in `smoothDivisorFamilyChoices κ R` is imposed on every
individual divisor.  It therefore couples the prime choices and does not
give an exact Euler product.  This file uses only the honest one-sided
comparison: a squarefree paired divisor family is injected into the larger
space in which, independently for every prime `p ≤ R`, an arbitrary subset
of the `2 * card κ` divisor occurrences may contain `p`.

The empty subset has weight one.  Every nonempty subset has weight `p⁻¹`,
because `p` then occurs in the global LCM.  Summing over the unrestricted
assignment space gives the finite product

`∏ p ∈ Nat.primesLE R, (1 + (2 ^ (2 * card κ) - 1) / p)`.

Only the injection into that space is used; no false equality with the
coordinatewise-truncated divisor family is asserted.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-! ## Prime-occurrence assignments -/













/-! ## The unrestricted assignment sum -/





/-! ## Encoding supported divisor families -/



















/-! ## Möbius mass as the squarefree indicator -/







@[simp]
theorem mem_squarefreeSmoothPairedDivisorChoices
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z : κ → ℕ × ℕ} :
    z ∈ squarefreeSmoothPairedDivisorChoices κ R ↔
      z ∈ smoothDivisorFamilyChoices κ R ∧
        SquarefreePairedDivisorChoice z := by
  classical
  simp [squarefreeSmoothPairedDivisorChoices]



/-! ## The harmonic LCM Euler majorant -/









/-! ## Selected and Selberg-scaled corollaries -/

















end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Canonical divisor truncation bounds

This file closes the purely infinite-series part of the canonical
fixed-carry expansion and isolates the genuinely coordinatewise part.

For a fixed prime-local factor with summable local errors, the sums over
subsets of the primes at most `X` converge to the full unrestricted
prime-support series.  This applies in particular to every fixed
carry-adjusted affine family satisfying the usual coefficient hypotheses.

The remaining divisor-cutoff discrepancy is bounded fiberwise by an
explicit finite quantity: the number of coordinatewise-admissible
squarefree divisor families in the support fiber, plus the unrestricted
primewise coefficient majorant.  Thus no infinite-series truncation remains
hidden in that discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology

/-! ## Exhaustion of natural primes -/







/-! ## Finite powersets converge to the unrestricted support series -/





/-! ## Fixed canonical carry families -/









/-! ## Coordinatewise support-fiber bounds -/



theorem mem_coordinatewiseTruncatedSupportFiber
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {P : Finset Nat.Primes}
    {support : FixedFamilyPrimeSupportAssignment κ P}
    {z : κ → ℕ × ℕ} :
    z ∈ coordinatewiseTruncatedSupportFiber R P support ↔
      z ∈ SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R ∧
        fixedFamilyPrimeSupportAssignmentOf P z = support := by
  classical
  simp [coordinatewiseTruncatedSupportFiber]



theorem coordinatewiseTruncatedSupportCoefficient_eq_sum_fiber
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    coordinatewiseTruncatedSupportCoefficient
        χ R P t u support =
      ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
        χ.transformedPairedDivisorFamily R z (t, u) := by
  classical
  rfl















/-! ## The named carry-weighted truncation majorant -/









end Wikipedia.SzemeredisTheorem

end

section


/-!
# Full-space cancellation of the canonical divisor truncation error

Fourier inversion sees the unrestricted primewise divisor expansion as a
finite sum over squarefree paired divisor families.  Terms whose left or
right divisor has crossed the coordinatewise cutoff have zero full-space
integral, because the smooth cutoff is supported in `(-∞, 1)`.  Thus the
unrestricted integral is exactly the coordinatewise-truncated integral.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff





end SmoothSieveCutoff

/-! ## The three paired states at every active prime/form incidence -/













/-! ## The squarefree divisor family encoded by a state assignment -/





@[simp]
theorem mem_fixedFamilyPairedPrimeStateLeftPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 1 := by
  classical
  simp [fixedFamilyPairedPrimeStateLeftPrimes]

@[simp]
theorem mem_fixedFamilyPairedPrimeStateRightPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 0 := by
  classical
  simp [fixedFamilyPairedPrimeStateRightPrimes]





















theorem prime_dvd_fixedFamilyPairedPrimeStatePrimeProduct_iff_mem
    {P : Finset Nat.Primes}
    (s : Finset {p // p ∈ P}) (p : {p // p ∈ P}) :
    (p : ℕ) ∣ ∏ r ∈ s, (r : ℕ) ↔ p ∈ s := by
  constructor
  · intro hp
    obtain ⟨r, hr, hpr⟩ :=
      (p.1.prop.prime.dvd_finsetProd_iff
        (fun r : {p // p ∈ P} => (r : ℕ))).mp hp
    have heqNat : (r : ℕ) = (p : ℕ) :=
      (r.1.prop.dvd_iff_eq p.1.prop.ne_one).mp hpr
    have heq : r = p := by
      apply Subtype.ext
      apply Subtype.ext
      exact heqNat
    simpa [heq] using hr
  · intro hp
    exact Finset.dvd_prod_of_mem
      (fun r : {p // p ∈ P} => (r : ℕ)) hp

theorem prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_left_iff
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    (p : ℕ) ∣
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 1 := by
  classical
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  rw [
    prime_dvd_fixedFamilyPairedPrimeStatePrimeProduct_iff_mem,
    mem_fixedFamilyPairedPrimeStateLeftPrimes]

theorem prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_right_iff
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    (p : ℕ) ∣
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 0 := by
  classical
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  rw [
    prime_dvd_fixedFamilyPairedPrimeStatePrimeProduct_iff_mem,
    mem_fixedFamilyPairedPrimeStateRightPrimes]

theorem fixedFamilyPrimeSupportAssignmentOf_stateDivisorFamily
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    fixedFamilyPrimeSupportAssignmentOf P
        (fixedFamilyPairedPrimeStateDivisorFamily support A) =
      support := by
  funext p
  ext q
  simp only [fixedFamilyPrimeSupportAssignmentOf,
    mem_pairedPrimeSupport, pairedLocalModulus,
    p.1.prop.dvd_lcm,
    prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_left_iff,
    prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_right_iff]
  constructor
  · rintro (⟨hq, _hstate⟩ | ⟨hq, _hstate⟩)
    · exact hq
    · exact hq
  · intro hq
    by_cases hleft : A p ⟨q, hq⟩ = 1
    · right
      exact ⟨hq, by omega⟩
    · left
      exact ⟨hq, hleft⟩

theorem squarefree_fixedFamilyPairedPrimeStateDivisorFamily
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    SquarefreePairedDivisorChoice
      (fixedFamilyPairedPrimeStateDivisorFamily support A) := by
  classical
  intro q
  constructor <;>
    unfold fixedFamilyPairedPrimeStateDivisorFamily <;>
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p _hp r _hr hpr
    change IsRelPrime (p : ℕ) (r : ℕ)
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes p.1.prop r.1.prop).mpr
      (fun heq =>
        hpr (by
          apply Subtype.ext
          apply Subtype.ext
          exact heq))
  · intro p _hp
    exact p.1.prop.squarefree
  · intro p _hp r _hr hpr
    change IsRelPrime (p : ℕ) (r : ℕ)
    apply Nat.coprime_iff_isRelPrime.mp
    exact (Nat.coprime_primes p.1.prop r.1.prop).mpr
      (fun heq =>
        hpr (by
          apply Subtype.ext
          apply Subtype.ext
          exact heq))
  · intro p _hp
    exact p.1.prop.squarefree

theorem fixedFamilyPairedPrimeStateDivisorFamily_injective
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    Function.Injective
      (fixedFamilyPairedPrimeStateDivisorFamily support) := by
  classical
  intro A B hAB
  funext p q
  have hzq :
      fixedFamilyPairedPrimeStateDivisorFamily support A q.1 =
        fixedFamilyPairedPrimeStateDivisorFamily support B q.1 :=
    congrFun hAB q.1
  have hleft :
      (A p q ≠ 1) ↔ (B p q ≠ 1) := by
    have hdiv :
        ((p : ℕ) ∣
            (fixedFamilyPairedPrimeStateDivisorFamily
              support A q.1).1) ↔
          ((p : ℕ) ∣
            (fixedFamilyPairedPrimeStateDivisorFamily
              support B q.1).1) := by
      rw [hzq]
    rw [
      prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_left_iff,
      prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_left_iff] at hdiv
    simpa only [q.2, exists_true_left,
      Subtype.coe_eta, proof_irrel_heq] using hdiv
  have hright :
      (A p q ≠ 0) ↔ (B p q ≠ 0) := by
    have hdiv :
        ((p : ℕ) ∣
            (fixedFamilyPairedPrimeStateDivisorFamily
              support A q.1).2) ↔
          ((p : ℕ) ∣
            (fixedFamilyPairedPrimeStateDivisorFamily
              support B q.1).2) := by
      rw [hzq]
    rw [
      prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_right_iff,
      prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_right_iff] at hdiv
    simpa only [q.2, exists_true_left,
      Subtype.coe_eta, proof_irrel_heq] using hdiv
  generalize ha : A p q = a at hleft hright
  generalize hb : B p q = b at hleft hright ⊢
  fin_cases a <;> fin_cases b <;> simp_all











theorem fixedFamilyPairedPrimeStateDivisorFamily_pos
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) :
    0 <
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 ∧
      0 <
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 := by
  classical
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  constructor <;>
    exact Finset.prod_pos fun p _hp => p.1.prop.pos





@[simp]
theorem mem_coordinatewiseAdmissiblePairedPrimeStateAssignments
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ}
    {support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R)}
    {A : FixedFamilyPairedPrimeStateAssignment support} :
    A ∈ coordinatewiseAdmissiblePairedPrimeStateAssignments R support ↔
      fixedFamilyPairedPrimeStateDivisorFamily support A ∈
        smoothDivisorFamilyChoices κ R := by
  classical
  simp [coordinatewiseAdmissiblePairedPrimeStateAssignments]

theorem stateDivisorFamily_mem_coordinatewiseTruncatedSupportFiber_iff
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ}
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R))
    (A : FixedFamilyPairedPrimeStateAssignment support) :
    fixedFamilyPairedPrimeStateDivisorFamily support A ∈
        coordinatewiseTruncatedSupportFiber
          R (primesLEAsPrimes R) support ↔
      fixedFamilyPairedPrimeStateDivisorFamily support A ∈
        smoothDivisorFamilyChoices κ R := by
  rw [mem_coordinatewiseTruncatedSupportFiber,
    SmoothSieveCutoff.mem_squarefreeSmoothPairedDivisorChoices]
  simp [
    squarefree_fixedFamilyPairedPrimeStateDivisorFamily,
    fixedFamilyPrimeSupportAssignmentOf_stateDivisorFamily]

theorem sum_admissible_stateCoefficients_eq_sum_coordinatewiseFiber
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R)) :
    (∑ A ∈ coordinatewiseAdmissiblePairedPrimeStateAssignments R support,
        (smoothDivisorFamilyCoefficient χ.toFun R
          (fixedFamilyPairedPrimeStateDivisorFamily support A) : ℂ)) =
      ∑ z ∈ coordinatewiseTruncatedSupportFiber
          R (primesLEAsPrimes R) support,
        (smoothDivisorFamilyCoefficient χ.toFun R z : ℂ) := by
  classical
  apply Finset.sum_bij
    (fun A _hA =>
      fixedFamilyPairedPrimeStateDivisorFamily support A)
  · intro A hA
    exact
      (stateDivisorFamily_mem_coordinatewiseTruncatedSupportFiber_iff
        support A).2
        (mem_coordinatewiseAdmissiblePairedPrimeStateAssignments.mp hA)
  · intro A _hA B _hB hAB
    exact fixedFamilyPairedPrimeStateDivisorFamily_injective support hAB
  · intro z hz
    have hzData :=
      (mem_coordinatewiseTruncatedSupportFiber.mp hz)
    have hzSquarefreeData :=
      SmoothSieveCutoff.mem_squarefreeSmoothPairedDivisorChoices.mp
        hzData.1
    let A :=
      fixedFamilyPairedPrimeStateAssignmentOf support z
    have hencode :
        fixedFamilyPairedPrimeStateDivisorFamily support A = z :=
      fixedFamilyPairedPrimeStateDivisorFamily_assignmentOf_eq
        support z hzSquarefreeData.1 hzSquarefreeData.2 hzData.2
    refine ⟨A, ?_, hencode⟩
    rw [mem_coordinatewiseAdmissiblePairedPrimeStateAssignments,
      hencode]
    exact hzSquarefreeData.1
  · intro A _hA
    rfl

theorem sum_all_stateCoefficients_eq_sum_admissible
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R)
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R)) :
    (∑ A : FixedFamilyPairedPrimeStateAssignment support,
        (smoothDivisorFamilyCoefficient χ.toFun R
          (fixedFamilyPairedPrimeStateDivisorFamily support A) : ℂ)) =
      ∑ A ∈ coordinatewiseAdmissiblePairedPrimeStateAssignments R support,
        (smoothDivisorFamilyCoefficient χ.toFun R
          (fixedFamilyPairedPrimeStateDivisorFamily support A) : ℂ) := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro A _hA hAadmissible
  have hnot :
      fixedFamilyPairedPrimeStateDivisorFamily support A ∉
        smoothDivisorFamilyChoices κ R := by
    simpa [coordinatewiseAdmissiblePairedPrimeStateAssignments] using
      hAadmissible
  rw [χ.smoothDivisorFamilyCoefficient_eq_zero_of_not_mem
    hR
    (fixedFamilyPairedPrimeStateDivisorFamily support A)
    (fixedFamilyPairedPrimeStateDivisorFamily_pos support A)
    hnot]
  exact_mod_cast (show (0 : ℝ) = 0 by rfl)

/-! ## Fourier integration of one support fiber -/







theorem integrable_coordinatewiseTruncatedSupportCoefficient
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    (R : ℕ) (P : Finset Nat.Primes)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    Integrable
      (fun tu : (κ → ℝ) × (κ → ℝ) =>
        coordinatewiseTruncatedSupportCoefficient
          χ R P tu.1 tu.2 support)
      (volume.prod volume) := by
  apply integrable_finsetSum
  intro z _hz
  exact χ.integrable_transformedPairedDivisorFamily R z

theorem integral_coordinatewiseTruncatedSupportCoefficient_eq_sum_fiber
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    (R : ℕ) (P : Finset Nat.Primes)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        coordinatewiseTruncatedSupportCoefficient
          χ R P tu.1 tu.2 support
        ∂(volume.prod volume)) =
      ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
        (smoothDivisorFamilyCoefficient χ.toFun R z : ℂ) := by
  calc
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        coordinatewiseTruncatedSupportCoefficient
          χ R P tu.1 tu.2 support
        ∂(volume.prod volume)) =
        ∫ tu : (κ → ℝ) × (κ → ℝ),
          ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
            χ.transformedPairedDivisorFamily R z tu
          ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact ae_of_all _ fun tu =>
        coordinatewiseTruncatedSupportCoefficient_eq_sum_fiber
          χ R P tu.1 tu.2 support
    _ = _ := by
      rw [MeasureTheory.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro z _hz
        exact
          (χ.smoothDivisorFamilyCoefficient_eq_integral R z).symm
      · intro z _hz
        exact χ.integrable_transformedPairedDivisorFamily R z

theorem integral_coordinatewiseTruncationSupportDiscrepancy_eq_zero
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R)
    (support :
      FixedFamilyPrimeSupportAssignment κ (primesLEAsPrimes R)) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        coordinatewiseTruncationSupportDiscrepancy
          χ R (primesLEAsPrimes R) tu.1 tu.2 support
        ∂(volume.prod volume)) = 0 := by
  have htruncated :
      (∫ tu : (κ → ℝ) × (κ → ℝ),
          coordinatewiseTruncatedSupportCoefficient
            χ R (primesLEAsPrimes R) tu.1 tu.2 support
          ∂(volume.prod volume)) =
        ∑ z ∈ coordinatewiseTruncatedSupportFiber
            R (primesLEAsPrimes R) support,
          (smoothDivisorFamilyCoefficient χ.toFun R z : ℂ) :=
    integral_coordinatewiseTruncatedSupportCoefficient_eq_sum_fiber
      χ R (primesLEAsPrimes R) support
  have hunrestricted :
      (∫ tu : (κ → ℝ) × (κ → ℝ),
          pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            fixedFamilyPrimeSupportCoefficient
              R tu.1 tu.2 support
          ∂(volume.prod volume)) =
        ∑ z ∈ coordinatewiseTruncatedSupportFiber
            R (primesLEAsPrimes R) support,
          (smoothDivisorFamilyCoefficient χ.toFun R z : ℂ) := by
    rw [
      integral_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient_eq_sum_states,
      sum_all_stateCoefficients_eq_sum_admissible χ hR support,
      sum_admissible_stateCoefficients_eq_sum_coordinatewiseFiber]
  unfold coordinatewiseTruncationSupportDiscrepancy
  rw [integral_sub
    (integrable_coordinatewiseTruncatedSupportCoefficient
      χ R (primesLEAsPrimes R) support)
    (integrable_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient
      χ R support),
    htruncated, hunrestricted, sub_self]

theorem integrable_coordinatewiseTruncationSupportDiscrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    (R : ℕ) (P : Finset Nat.Primes)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    Integrable
      (fun tu : (κ → ℝ) × (κ → ℝ) =>
        coordinatewiseTruncationSupportDiscrepancy
          χ R P tu.1 tu.2 support)
      (volume.prod volume) :=
  (integrable_coordinatewiseTruncatedSupportCoefficient
      χ R P support).sub
    (integrable_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient
      χ R support)



end Wikipedia.SzemeredisTheorem

end
/-!
# Full-space cancellation of the canonical divisor truncation error

Fourier inversion sees the unrestricted primewise divisor expansion as a
finite sum over squarefree paired divisor families.  Terms whose left or
right divisor has crossed the coordinatewise cutoff have zero full-space
integral, because the smooth cutoff is supported in `(-∞, 1)`.  Thus the
unrestricted integral is exactly the coordinatewise-truncated integral.
-/
open Wikipedia.SzemeredisTheorem
open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators
/-! ## The three paired states at every active prime/form incidence -/
/-! ## The squarefree divisor family encoded by a state assignment -/
/-! ## Fourier integration of one support fiber -/

open Wikipedia.SzemeredisTheorem in
/-- Full-space Fourier inversion cancels the complete carry-weighted
coordinatewise truncation discrepancy.  No arithmetic hypothesis on the
canonical affine families is needed. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) {R : ℕ} (hR : 2 ≤ R)
    (forms : κ → CFZFormIndex k) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        cfzCanonicalCarryTruncationDiscrepancy
          (N := N) χ W b R forms tu.1 tu.2
        ∂(volume.prod volume)) = 0 := by
  classical
  unfold cfzCanonicalCarryTruncationDiscrepancy
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro carry _hcarry
    rw [integral_const_mul]
    apply mul_eq_zero_of_right
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro support _hsupport
      rw [integral_mul_const,
        integral_coordinatewiseTruncationSupportDiscrepancy_eq_zero
          χ (by omega : 1 < R) support,
        zero_mul]
    · intro support _hsupport
      exact
        (integrable_coordinatewiseTruncationSupportDiscrepancy
          χ R (primesLEAsPrimes R) support).mul_const
          (cfzCanonicalCarryPrimeSupportDensity
            N W b forms carry support)
  · intro carry _hcarry
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro support _hsupport
    exact
      (integrable_coordinatewiseTruncationSupportDiscrepancy
        χ R (primesLEAsPrimes R) support).mul_const
        (cfzCanonicalCarryPrimeSupportDensity
          N W b forms carry support)
