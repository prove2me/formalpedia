-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.selectedCFZCarryAdjustedFamilyAtVector_goodPrime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:41:56.544271+00:00
-- url     : https://prove2.me/submissions/19990301-d037-45b2-a660-8180c61deba7

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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryFourierNormalization
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCyclicBoundaryLimit
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_affineRankTwoGoodPrime_cfzCarryAdjusted
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_cfzCoefficient_support_separating
import Theorems.Thm_Wikipedia_SzemeredisTheorem_minor_natAbs_le_exceptionalPrimeBound

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Independence of the Conlon--Fox--Zhao forms

The Goldston--Yıldırım linear-forms estimate requires the coefficient vectors
of distinct forms to be nonzero and pairwise non-proportional.  This file
records those facts over `ℤ` for the concrete CFZ family.
-/

namespace Wikipedia.SzemeredisTheorem











@[simp]
theorem cfzCoefficient_selected {k : ℕ} (q : CFZFormIndex k)
    (i : {i : Fin k // i ≠ q.1}) :
    cfzCoefficient q (i.1, q.2 i) =
      (i.1 : ℤ) - (q.1 : ℤ) := by
  simp [cfzCoefficient, i.2]





theorem cfzCoefficient_selected_ne_zero {k : ℕ}
    (q : CFZFormIndex k) (i : {i : Fin k // i ≠ q.1}) :
    cfzCoefficient q (i.1, q.2 i) ≠ 0 := by
  rw [cfzCoefficient_selected]
  apply sub_ne_zero.mpr
  intro h
  apply i.2
  apply Fin.ext
  exact_mod_cast h

/-- For `k ≥ 2`, every CFZ form has a nonzero integer coefficient. -/
theorem exists_cfzCoefficient_ne_zero {k : ℕ} (hk : 2 ≤ k)
    (q : CFZFormIndex k) :
    ∃ v : CFZVariable k, cfzCoefficient q v ≠ 0 := by
  have hcard : 1 < Fintype.card (Fin k) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨i, hi⟩ :=
    Fintype.exists_ne_of_one_lt_card hcard q.1
  let i' : {i : Fin k // i ≠ q.1} := ⟨i, hi⟩
  exact ⟨(i, q.2 i'), cfzCoefficient_selected_ne_zero q i'⟩

/-- Equivalently, the coefficient vector of every CFZ form is nonzero. -/
theorem cfzCoefficient_ne_zero {k : ℕ} (hk : 2 ≤ k)
    (q : CFZFormIndex k) :
    cfzCoefficient q ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_cfzCoefficient_ne_zero hk q
  intro hzero
  exact hv (congrFun hzero v)





/-- At the weakest bound ensuring that every individual form is nonzero, the
CFZ coefficient vectors are pairwise non-proportional. -/
theorem cfzCoefficients_pairwise_not_proportional {k : ℕ} (hk : 2 ≤ k) :
    Pairwise fun q r : CFZFormIndex k =>
      ¬ IntCoefficientProportional
        (cfzCoefficient q) (cfzCoefficient r) := by
  intro q r hqr hproportional
  obtain ⟨v, hqv, hrv⟩ :=
    exists_cfzCoefficient_support_separating q r hqr
  obtain ⟨w, hqw⟩ := exists_cfzCoefficient_ne_zero hk q
  have hminor := hproportional v w
  have hright :
      cfzCoefficient q w * cfzCoefficient r v ≠ 0 :=
    mul_ne_zero hqw hrv
  apply hright
  simpa [hqv] using hminor.symm

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

theorem cfzAffineForms_nonzero {k : ℕ} (hk : 2 ≤ k) :
    NonzeroCoefficientVectors
      (fun q : CFZFormIndex k => cfzAffineForm q) :=
  fun q => cfzCoefficient_ne_zero hk q

theorem cfzAffineForms_pairwiseIndependent {k : ℕ}
    (hk : 2 ≤ k) :
    PairwiseIndependentCoefficients
      (fun q : CFZFormIndex k => cfzAffineForm q) :=
  cfzCoefficients_pairwise_not_proportional hk





end Wikipedia.SzemeredisTheorem

end

section


/-!
# Explicit exceptional moduli for integer affine forms

The local-factor argument needs a finite bound after which every selected
nonzero coefficient and every selected nonzero two-by-two minor remains
nonzero modulo `p`.  We use a deliberately coarse sum of absolute values;
its advantage is that it is total, explicit, and requires no choices.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm



end AffineForm

theorem intCast_zmod_ne_zero_of_natAbs_lt
    {p : ℕ} {z : ℤ} (hz : z ≠ 0)
    (hzp : Int.natAbs z < p) :
    (z : ZMod p) ≠ 0 := by
  intro hzero
  have hpdivInt : (p : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzero
  have hpdiv : p ∣ Int.natAbs z := by
    simpa using
      (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := z)).2 hpdivInt
  have hzpos : 0 < Int.natAbs z :=
    (Int.natAbs_pos.mpr hz)
  have hple : p ≤ Int.natAbs z :=
    Nat.le_of_dvd hzpos hpdiv
  omega



theorem coefficient_natAbs_le_exceptionalPrimeBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ) (q : κ) (i : ι) :
    Int.natAbs ((forms q).coefficient i) ≤
      exceptionalPrimeBound forms := by
  have hi :
      Int.natAbs ((forms q).coefficient i) ≤
        ∑ j : ι, Int.natAbs ((forms q).coefficient j) :=
    Finset.single_le_sum
      (f := fun j : ι =>
        Int.natAbs ((forms q).coefficient j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hq :
      (∑ j : ι, Int.natAbs ((forms q).coefficient j)) ≤
        ∑ r : κ, ∑ j : ι,
          Int.natAbs ((forms r).coefficient j) :=
    Finset.single_le_sum
      (f := fun r : κ =>
        ∑ j : ι, Int.natAbs ((forms r).coefficient j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  exact (hi.trans hq).trans (Nat.le_add_right _ _)



/-- Failure of proportionality produces a nonzero coefficient minor. -/
theorem exists_coefficientMinor_ne_zero
    {ι : Type*} {ψ φ : AffineForm ι ℤ}
    (h : ¬IntCoefficientProportional
      ψ.coefficient φ.coefficient) :
    ∃ i j, ψ.coefficientMinor φ i j ≠ 0 := by
  by_contra hzero
  push Not at hzero
  apply h
  intro i j
  exact sub_eq_zero.mp (hzero i j)

/-- Beyond the explicit bound, every nonzero coefficient vector retains a
nonzero coefficient modulo `p`. -/
theorem exists_coefficient_cast_ne_zero_of_bound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : NonzeroCoefficientVectors forms)
    {p : ℕ} (hp : exceptionalPrimeBound forms < p)
    (q : κ) :
    ∃ i : ι, ((forms q).coefficient i : ZMod p) ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (hforms q)
  refine ⟨i, intCast_zmod_ne_zero_of_natAbs_lt hi ?_⟩
  exact (coefficient_natAbs_le_exceptionalPrimeBound forms q i).trans_lt hp

/-- Beyond the explicit bound, every minor witnessing pairwise
independence remains nonzero modulo `p`. -/
theorem exists_minor_cast_ne_zero_of_bound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms)
    {p : ℕ} (hp : exceptionalPrimeBound forms < p)
    {q r : κ} (hqr : q ≠ r) :
    ∃ i j : ι,
      (((forms q).coefficientMinor (forms r) i j : ℤ) :
        ZMod p) ≠ 0 := by
  obtain ⟨i, j, hij⟩ :=
    exists_coefficientMinor_ne_zero (hforms hqr)
  refine ⟨i, j, intCast_zmod_ne_zero_of_natAbs_lt hij ?_⟩
  exact (minor_natAbs_le_exceptionalPrimeBound forms q r i j).trans_lt hp

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Rank-two affine densities at good primes

For a finite system of affine forms, failure of rank two modulo `p` is
detected by the vanishing of every two-by-two coefficient minor for some
distinct pair.  This file isolates a finite, explicit exceptional set using
the sum of the absolute values of all such minors.

Outside that set, pairwise independent integer coefficient vectors remain
rank two modulo `p`.  Thus every selected subfamily containing two distinct
indices has common-zero density at most `1 / p²`: its common-zero set is
contained in the common-zero set of one rank-two pair.  This is the actual
higher-order density estimate needed for the CFZ family.  Repeated indices do
not create rank, so the hypotheses use a `Finset` and explicitly require it
to be nontrivial.

The final results instantiate
`HasGoodPrimeHigherOrderDensityEstimate` for the CFZ forms and package the
estimate together with the exact local-factor inclusion--exclusion formula.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## An explicit finite exceptional set for rank two -/















/-- The older all-purpose exceptional bound also implies the exact
rank-two good-prime condition. -/
theorem affineRankTwoGoodPrime_of_exceptionalPrimeBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms)
    {p : ℕ} (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) :
    AffineRankTwoGoodPrime p forms := by
  refine ⟨hp, ?_⟩
  intro q r hqr
  exact exists_minor_cast_ne_zero_of_bound
    hforms hlarge hqr



/-! ## Selected-family rank and density -/

















/-! ## CFZ specialization -/



















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



/-- The usual integer exceptional bound supplies the direct modular
one-form predicate for the original, unscaled system. -/
theorem affineNonzeroGoodPrime_of_exceptionalPrimeBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    {p : ℕ} (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) :
    AffineNonzeroGoodPrime p forms := by
  refine ⟨hp, fun q => ?_⟩
  exact exists_coefficient_cast_ne_zero_of_bound
    hnonzero hlarge q

/-- Direct modular nondegeneracy is inherited by an arbitrary reindexed
subfamily. -/
theorem AffineNonzeroGoodPrime.comp
    {κ κ' ι : Type*} [Fintype ι]
    {p : ℕ} {forms : κ → AffineForm ι ℤ}
    (hgood : AffineNonzeroGoodPrime p forms)
    (f : κ' → κ) :
    AffineNonzeroGoodPrime p (fun q => forms (f q)) := by
  exact ⟨hgood.1, fun q => hgood.2 (f q)⟩

/-- Rank-two good-prime geometry is inherited by an injectively reindexed
subfamily. -/
theorem AffineRankTwoGoodPrime.comp
    {κ κ' ι : Type*} [Fintype κ] [Fintype κ'] [Fintype ι]
    {p : ℕ} {forms : κ → AffineForm ι ℤ}
    (hgood : AffineRankTwoGoodPrime p forms)
    (f : κ' → κ) (hf : Function.Injective f) :
    AffineRankTwoGoodPrime p (fun q => forms (f q)) := by
  refine ⟨hgood.1, ?_⟩
  intro q r hqr
  exact hgood.2 (hf.ne hqr)

/-! ## Scaling identities and W-trick preservation -/



/-- At a modulus not dividing `W`, its residue class is nonzero. -/
theorem natCast_zmod_ne_zero_of_not_dvd
    {W p : ℕ} (hpW : ¬p ∣ W) :
    (W : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hpW

/-- A nonzero modular coefficient survives W-scaling. -/
theorem wTrickedAffineForm_coefficient_cast_ne_zero
    {ι : Type*} {W b p : ℕ} (hp : p.Prime)
    (hpW : ¬p ∣ W) (ψ : AffineForm ι ℤ)
    {i : ι} (hi : (ψ.coefficient i : ZMod p) ≠ 0) :
    ((wTrickedAffineForm W b ψ).coefficient i : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  simp only [wTrickedAffineForm_coefficient, Int.cast_mul,
    Int.cast_natCast]
  exact mul_ne_zero
    (natCast_zmod_ne_zero_of_not_dvd hpW) hi











/-! ## Exact one- and two-form densities -/









/-! ## Complex first-order expansion from modular geometry -/





/-! ## Stable complex and paired-Fourier ratios -/







/-! ## Direct comparison with the zeta Euler model -/





/-! ## Uniform selected-CFZ specialization -/











/-- Every selected original CFZ family has direct modular one-form geometry
above the full-family k-only exceptional bound. -/
theorem selectedCFZAffineNonzeroGoodPrime
    {k p : ℕ} (hk : 2 ≤ k)
    (hp : p.Prime)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (e : LinearFormsExponent k) :
    AffineNonzeroGoodPrime p
      (fun q : SelectedCFZFormIndex e =>
        cfzAffineForm q.1) := by
  exact
    (affineNonzeroGoodPrime_of_exceptionalPrimeBound
      (cfzAffineForms_nonzero hk) hp hlarge).comp
        (fun q : SelectedCFZFormIndex e => q.1)

/-- Every selected original CFZ family has direct modular rank-two geometry
above the same full-family k-only exceptional bound. -/
theorem selectedCFZAffineRankTwoGoodPrime
    {k p : ℕ} (hk : 2 ≤ k)
    (hp : p.Prime)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (e : LinearFormsExponent k) :
    AffineRankTwoGoodPrime p
      (fun q : SelectedCFZFormIndex e =>
        cfzAffineForm q.1) := by
  exact
    (affineRankTwoGoodPrime_of_exceptionalPrimeBound
      (cfzAffineForms_pairwiseIndependent hk) hp hlarge).comp
        (fun q : SelectedCFZFormIndex e => q.1)
        Subtype.coe_injective











end Wikipedia.SzemeredisTheorem

end

section



/-!
# Carry-block boundaries for the cyclic CFZ lift

The standard representative of a CFZ form modulo `N` is not periodic in the
natural input coordinates.  This file gives the unconditional replacement
for the false periodicity step.

We divide the standard box into coordinatewise quotient blocks of side `D`.
On a block where every selected CFZ carry is constant, the cyclic lift is an
ordinary affine form with a carry-dependent constant.  A block on which one
carry changes must cross a hyperplane at an integral multiple of `N`.
Because CFZ coefficients are bounded and every CFZ form has a coefficient
equal to `1` or `-1`, the union of all such blocks has an explicit
codimension-one cardinality bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Coordinate quotient blocks -/



















/-! ## A generic unit-coefficient strip count -/









/-! ## CFZ coefficient and block-diameter facts -/





/-! ## Carry-change hyperplanes -/

























/-! ## Explicit bad-point counts -/

















/-! ## Carry-adjusted affine block model -/













@[simp]
theorem cfzCarryAdjustedAffineForm_coefficient
    {k : ℕ} (N W b : ℕ)
    (q : CFZFormIndex k) (c : ℤ)
    (v : CFZVariable k) :
    (cfzCarryAdjustedAffineForm N W b q c).coefficient v =
      (W : ℤ) * cfzCoefficient q v := by
  rfl

















/-! ## A normalized disagreement bound -/





















/-! ## Carry-dependent affine residue model -/















end Wikipedia.SzemeredisTheorem

end

section




/-!
# Carry-block Euler products for selected CFZ families

The cyclic CFZ lift is not globally periodic modulo a paired divisor LCM:
crossing a representative boundary changes an integer carry.  The preceding
carry-block boundary file replaces that false periodicity by a sound
piecewise-affine model.  This file identifies the exact arithmetic model on
each complete quotient block.

For `D = pairedDivisorLcm z`, a complete block has the form

`x = r + D a`,  with `0 ≤ r_v < D`.

The carry is frozen at the lower corner `D a`.  Thus the block is governed
by the family

`q ↦ cfzCarryAdjustedAffineForm N W b q (cfzCarry q (D a))`.

Its mean over `r` is an exact squarefree CRT Euler product.  Averaging those
products over all complete blocks gives the global blockwise Euler model.
The only losses in comparing it with the original cyclic density are:

* the explicit carry-transition density from `CFZCarryBlockBoundary`;
* the outer partial-block boundary of size
  `O(D * card(CFZVariable k) / N)`.

The affine constants may depend arbitrarily on the block and on the form.
At primes dividing `W` they are still congruent to the reduced residue `b`,
so every supported local density is zero.  At good primes outside `W`,
one-form and rank-two geometry depends only on the coefficients, giving the
usual exact cardinality-at-most-two formula and the uniform `p⁻²` bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A generic natural representative for an affine residue -/









/-! ## Complete quotient blocks and their affine families -/









/-! ## Good complete quotient blocks -/













/-! ## Exact blockwise CRT and averaged Euler products -/







/-! ## The complete-block mean is the averaged Euler product -/



/-! ## The outer partial-block boundary -/







/-! ## Unconditional cyclic-to-Euler approximation -/









/-! ## Selected-family specialization -/









/-! ## Carry-dependent constants and primes dividing `W` -/



















/-! ## Good primes outside `W` -/



/-- Direct modular one-form geometry survives arbitrary carry-dependent
integer constants whenever `p ∤ W`. -/
theorem affineNonzeroGoodPrime_cfzCarryAdjusted
    {κ : Type*} {k p : ℕ}
    (N W b : ℕ) (forms : κ → CFZFormIndex k)
    (c : κ → ℤ)
    (hgood : AffineNonzeroGoodPrime p
      (fun q => cfzAffineForm (forms q)))
    (hpW : ¬p ∣ W) :
    AffineNonzeroGoodPrime p
      (fun q =>
        cfzCarryAdjustedAffineForm
          N W b (forms q) (c q)) := by
  refine ⟨hgood.1, fun q => ?_⟩
  obtain ⟨i, hi⟩ := hgood.2 q
  refine ⟨i, ?_⟩
  have hw :=
    wTrickedAffineForm_coefficient_cast_ne_zero
      (W := W) (b := 0) (p := p)
      hgood.1 hpW (cfzAffineForm (forms q)) hi
  simpa only [cfzCarryAdjustedAffineForm_coefficient,
    wTrickedAffineForm_coefficient,
    cfzAffineForm_coefficient] using hw















end Wikipedia.SzemeredisTheorem

end
/-!
# Fourier normalization for canonical CFZ carry vectors

The canonical divisor expansion freezes one complete integer carry vector,
rather than a divisor-dependent quotient block.  This file gives that
carry-vector model the same local-ratio, Euler-tail, factorization, and
normalized Fourier API as the older carry-block model.

All estimates are uniform in the carry vector.  In particular, no
realizability or positive-density hypothesis is imposed: vectors which do
not occur in a canonical carry cell satisfy the same pointwise arithmetic
statements.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology
open scoped BigOperators
/-! ## Packaged canonical carry-vector data -/
/-! ## Direct good-prime geometry -/

open Wikipedia.SzemeredisTheorem in
/-- Above the exceptional cutoff of the original full CFZ family and
outside `W`, an arbitrary selected carry vector has direct modular
one-form and rank-two geometry.  The affine constants `N`, `b`, and
`carry` are completely unrestricted. -/
theorem solution
    {k N W b p : ℕ}
    (hk : 2 ≤ k) (hp : p.Prime) (hpW : ¬p ∣ W)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ) :
    AffineNonzeroGoodPrime p
        (cfzCarryAdjustedFamilyAtVector
          N W b
          (fun q : SelectedCFZFormIndex e => q.1) carry) ∧
      AffineRankTwoGoodPrime p
        (cfzCarryAdjustedFamilyAtVector
          N W b
          (fun q : SelectedCFZFormIndex e => q.1) carry) := by
  change
    AffineNonzeroGoodPrime p
        (fun q : SelectedCFZFormIndex e =>
          cfzCarryAdjustedAffineForm N W b q.1 (carry q)) ∧
      AffineRankTwoGoodPrime p
        (fun q : SelectedCFZFormIndex e =>
          cfzCarryAdjustedAffineForm N W b q.1 (carry q))
  exact
    ⟨affineNonzeroGoodPrime_cfzCarryAdjusted
        N W b
        (fun q : SelectedCFZFormIndex e => q.1) carry
        (selectedCFZAffineNonzeroGoodPrime hk hp hlarge e)
        hpW,
      affineRankTwoGoodPrime_cfzCarryAdjusted
        N W b
        (fun q : SelectedCFZFormIndex e => q.1) carry
        (selectedCFZAffineRankTwoGoodPrime hk hp hlarge e)
        hpW⟩
