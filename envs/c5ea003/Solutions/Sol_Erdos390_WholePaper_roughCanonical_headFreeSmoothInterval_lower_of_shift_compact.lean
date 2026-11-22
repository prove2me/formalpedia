-- Prove2me | solution 1 for Erdos390.WholePaper.roughCanonical_headFreeSmoothInterval_lower_of_shift_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:42:05.571762+00:00
-- url     : https://prove2.me/submissions/c0a6b161-e4ff-4c6a-82bb-89b47c83fb55

import Definitions.Def_erdos390_remaining_analytic_propositions_008
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound
import Definitions.Def_erdos390_analytic_foundations_006

/- Source module: Erdos390.Full.HeadPattern -/
section


/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern



namespace Pattern

variable (P : Pattern)











theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero













theorem gcd_modulus_ne_zero (k : ℕ) : Nat.gcd k P.modulus ≠ 0 := by
  intro hzero
  have := Nat.gcd_eq_zero_iff.mp hzero
  exact P.modulus_ne_zero this.2



theorem divisors_gcd_eq_filter (k : ℕ) :
    (Nat.gcd k P.modulus).divisors =
      P.modulus.divisors.filter (fun d ↦ d ∣ k) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · rintro ⟨hdgcd, _⟩
    exact ⟨⟨(Nat.dvd_gcd_iff.mp hdgcd).2, P.modulus_ne_zero⟩,
      (Nat.dvd_gcd_iff.mp hdgcd).1⟩
  · rintro ⟨⟨hdmod, _⟩, hdk⟩
    exact ⟨Nat.dvd_gcd hdk hdmod, P.gcd_modulus_ne_zero k⟩

/-- The gcd form of `coprimeWeight` is exactly the usual divisor sum
`∑_{d∣M_H} μ(d) 1_{d∣k}` from the paper. -/
theorem coprimeWeight_eq_divisor_sum (k : ℕ) :
    P.coprimeWeight k =
      ∑ d ∈ P.modulus.divisors,
        if d ∣ k then ArithmeticFunction.moebius d else 0 := by
  rw [coprimeWeight, P.divisors_gcd_eq_filter k, Finset.sum_filter]



end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.Full.StructuredCells -/
section


/-!
# Exact structured-cell reductions

This file defines the actual finite smooth intervals and exact head cells.
It proves the finite inclusion--exclusion identity before any use of a
friable-number asymptotic.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.StructuredCells

open HeadPattern













theorem smoothNumbersUpTo_mono {X₁ X₂ y : ℕ} (hX : X₁ ≤ X₂) :
    Nat.smoothNumbersUpTo X₁ (y + 1) ⊆
      Nat.smoothNumbersUpTo X₂ (y + 1) := by
  intro m hm
  rw [Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1.trans hX, hm.2⟩

/-- An exact interval count is a difference of two `psi` values. -/
theorem smoothInterval_card_eq_psi_sub {lo hi y : ℕ} (hlohi : lo ≤ hi) :
    (smoothInterval lo hi y).card = psi hi y - psi lo y := by
  have hset : smoothInterval lo hi y =
      Nat.smoothNumbersUpTo hi (y + 1) \
        Nat.smoothNumbersUpTo lo (y + 1) := by
    ext m
    simp only [mem_smoothInterval, Finset.mem_sdiff,
      Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨hlom, hmhi, hsmooth⟩
      exact ⟨⟨hmhi, hsmooth⟩, fun hlow ↦ (Nat.not_le_of_lt hlom) hlow.1⟩
    · rintro ⟨⟨hmhi, hsmooth⟩, hnotlow⟩
      refine ⟨?_, hmhi, hsmooth⟩
      by_contra hnlt
      exact hnotlow ⟨Nat.le_of_not_gt hnlt, hsmooth⟩
  rw [hset, Finset.card_sdiff]
  have hinter :
      Nat.smoothNumbersUpTo lo (y + 1) ∩
          Nat.smoothNumbersUpTo hi (y + 1) =
        Nat.smoothNumbersUpTo lo (y + 1) := by
    exact Finset.inter_eq_left.mpr (smoothNumbersUpTo_mono hlohi)
  rw [hinter]
  rfl











theorem modulus_mem_smoothNumbers (P : Pattern) {y : ℕ}
    (hhead : ∀ p ∈ P.primes, p ≤ y) :
    P.modulus ∈ Nat.smoothNumbers (y + 1) := by
  rw [Pattern.modulus]
  apply Finset.prod_induction (s := P.primes)
    (fun p ↦ p)
    (fun z ↦ z ∈ Nat.smoothNumbers (y + 1))
    (fun _ _ ha hb ↦ Nat.mul_mem_smoothNumbers ha hb)
    (by simp [Nat.mem_smoothNumbers])
  intro p hp
  exact Nat.mem_smoothNumbers_of_lt (P.prime_mem p hp).pos
    (Nat.lt_succ_of_le (hhead p hp))



/-- Exact reindexing of smooth multiples by division.  This is the finite
identity that turns each inclusion--exclusion term into a difference of two
friable counting functions. -/
theorem smooth_multiple_card_eq_quotient_interval {lo hi y D : ℕ}
    (hDpos : 0 < D) (hDsmooth : D ∈ Nat.smoothNumbers (y + 1)) :
    ((smoothInterval lo hi y).filter (D ∣ ·)).card =
      (smoothInterval (lo / D) (hi / D) y).card := by
  classical
  apply Finset.card_bij (fun m _ ↦ m / D)
  · intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hminterval, hDvd⟩ := hm
    obtain ⟨hlom, hmhi, hsmooth⟩ := mem_smoothInterval.mp hminterval
    apply mem_smoothInterval.mpr
    refine ⟨(Nat.div_lt_iff_lt_mul hDpos).mpr ?_,
      (Nat.le_div_iff_mul_le hDpos).mpr ?_, ?_⟩
    · simpa [Nat.div_mul_cancel hDvd] using hlom
    · simpa [Nat.div_mul_cancel hDvd] using hmhi
    · exact Nat.mem_smoothNumbers_of_dvd hsmooth (Nat.div_dvd_of_dvd hDvd)
  · intro m₁ hm₁ m₂ hm₂ heq
    rw [Finset.mem_filter] at hm₁ hm₂
    calc
      m₁ = m₁ / D * D := (Nat.div_mul_cancel hm₁.2).symm
      _ = m₂ / D * D := by rw [heq]
      _ = m₂ := Nat.div_mul_cancel hm₂.2
  · intro k hk
    refine ⟨k * D, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, by simp⟩
      obtain ⟨hlok, hkhi, hksmooth⟩ := mem_smoothInterval.mp hk
      apply mem_smoothInterval.mpr
      exact ⟨(Nat.div_lt_iff_lt_mul hDpos).mp hlok,
        (Nat.le_div_iff_mul_le hDpos).mp hkhi,
        Nat.mul_mem_smoothNumbers hksmooth hDsmooth⟩
    · exact Nat.mul_div_left k hDpos





end Erdos390.Full.StructuredCells

end

/- Source module: Erdos390.Full.FriableAsymptotic -/
section


/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/



















































/-! ## Explicit regularity of the finite Dickman kernel -/









/-! ## The Dickman test weight in the prime recurrence -/

























theorem friableCount_mono_left {X₁ X₂ y : ℕ} (hX : X₁ ≤ X₂) :
    friableCount X₁ y ≤ friableCount X₂ y := by
  apply Finset.card_le_card
  intro m hm
  rw [Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1.trans hX, hm.2⟩

























/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic






























/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/


















/-! ## Uniform floor stability for the recursive Dickman kernel -/





























































end Erdos390.Full.FriableAsymptotic

end

/- Source module: Erdos390.Full.MarkedFriableAsymptotic -/
section


open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology Asymptotics

namespace Erdos390.Full.MarkedFriableAsymptotic

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern

theorem psi_eq_friableCount (X y : ℕ) :
    psi X y = FriableAsymptotic.friableCount X y := rfl





end Erdos390.Full.MarkedFriableAsymptotic

end

/- Source module: Erdos390.Full.PaperScaleMarkedCell -/
section


/-!
# Paper-scale common main term for marked structured cells

The raw structured-cell asymptotic is a finite sum of endpoint Dickman
terms.  This module performs the algebraic closure required in the paper:
the head Möbius coefficient is evaluated exactly, and the endpoint terms
are compared with one common Dickman translate before normalization.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.PaperScaleMarkedCell

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic
open StructuredCellAsymptotic
open DivisibilityMomentBounds

noncomputable section

/-! ## Exact closure of the head Möbius coefficient -/



private theorem reciprocalAF_isMultiplicative :
    reciprocalAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [reciprocalAF], ?_⟩
  intro m n hm hn hcop
  simp only [reciprocalAF, ArithmeticFunction.coe_mk, hm, hn,
    mul_ne_zero hm hn, if_false, Nat.cast_mul]
  field_simp

private theorem modulus_squarefree (P : Pattern) : Squarefree P.modulus := by
  unfold Pattern.modulus
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (P.prime_mem p hp) (P.prime_mem q hq)).mpr hpq)
  · intro p hp
    exact (P.prime_mem p hp).squarefree

/-- The exact identity
`sum_{a | M_H} mu(a)/a = phi(M_H)/M_H`, in the real field used by the
analytic estimates. -/
theorem sum_moebius_div_inv_eq_totient_ratio (P : Pattern) :
    (∑ a ∈ P.modulus.divisors,
        (ArithmeticFunction.moebius a : ℝ) / (a : ℝ)) =
      (P.modulus.totient : ℝ) / (P.modulus : ℝ) := by
  have hprod := reciprocalAF_isMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    reciprocalAF (modulus_squarefree P)
  have hprod' :
      (∏ p ∈ P.modulus.primeFactors, (1 - 1 / (p : ℝ))) =
        ∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) := by
    calc
      _ = ∏ p ∈ P.modulus.primeFactors, (1 - reciprocalAF p) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
        simp [reciprocalAF, hp0]
      _ = ∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) * reciprocalAF a := hprod
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha0 := (Nat.pos_of_mem_divisors ha).ne'
        simp [reciprocalAF, ha0, div_eq_mul_inv]
  have htotQ := Nat.totient_eq_mul_prod_factors P.modulus
  have htotR :
      (P.modulus.totient : ℝ) =
        (P.modulus : ℝ) *
          ∏ p ∈ P.modulus.primeFactors, (1 - 1 / (p : ℝ)) := by
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) htotQ
    norm_num at hcast
    simpa [one_div] using hcast
  rw [← hprod']
  have hmod : (P.modulus : ℝ) ≠ 0 := by
    exact_mod_cast P.modulus_ne_zero
  apply (eq_div_iff hmod).2
  nlinarith







/-! ## The common paper-scale main term -/







































/-! ## Normalization algebra -/











end

end Erdos390.Full.PaperScaleMarkedCell

end

/- Source module: Erdos390.WholePaper.RoughHeadCompatibleFinitePoint -/
section


/-!
# The literal head-compatible finite raw point

This file constructs the first finite point in the guarded rough selector.
The upper block `E`, the high lower block `H`, and the broad lower block `J`
are literal natural-number half-open intervals.  Head freedom is imposed by
coprimality with the product of all primes up to `W`, and the raw weight is
defined pointwise from those finite sets.

The second half proves the exact deterministic identities used before any
HT--Saias or prime-number estimate: finite Möbius inclusion--exclusion,
reindexing of smooth multiples by division, and the resulting physical-block
shift through every divisor of the head modulus.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.HeadPattern
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Literal physical intervals -/





















/-! ## The finite head and raw weights -/









/-- The head modulus is always positive, including for an empty head. -/
theorem roughHeadModulus_pos (W : ℕ) :
    0 < roughHeadModulus W := by
  rw [← roughHeadZeroPattern_modulus]
  exact Nat.pos_of_ne_zero (roughHeadZeroPattern W).modulus_ne_zero







































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

/-- Exact finite Möbius inclusion--exclusion for head freedom on an
arbitrary finite set. -/
theorem roughHeadFree_card_eq_moebiusDivisorCounts
    (W : ℕ) (A : Finset ℕ) :
    ((roughHeadFree W A).card : ℤ) =
      ∑ d ∈ (roughHeadModulus W).divisors,
        ArithmeticFunction.moebius d *
          (((A.filter (d ∣ ·)).card : ℕ) : ℤ) := by
  let P : Erdos390.Full.HeadPattern.Pattern := roughHeadZeroPattern W
  rw [roughHeadFree, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  change
    (∑ a ∈ A,
      if Nat.Coprime a P.modulus then (1 : ℤ) else 0) =
      ∑ d ∈ P.modulus.divisors,
        ArithmeticFunction.moebius d *
          (((A.filter (d ∣ ·)).card : ℕ) : ℤ)
  calc
    (∑ a ∈ A,
        if Nat.Coprime a P.modulus then (1 : ℤ) else 0) =
      ∑ a ∈ A, ∑ d ∈ P.modulus.divisors,
        if d ∣ a then ArithmeticFunction.moebius d else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [← P.coprimeWeight_eq_indicator,
        P.coprimeWeight_eq_divisor_sum]
    _ = ∑ d ∈ P.modulus.divisors, ∑ a ∈ A,
        if d ∣ a then ArithmeticFunction.moebius d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ P.modulus.divisors,
        ArithmeticFunction.moebius d *
          (((A.filter (d ∣ ·)).card : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro d _hd
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero, Finset.mul_sum, mul_ite,
        mul_one, mul_zero]

/-- The head modulus is smooth at any cutoff `y ≥ W`; its divisors inherit
this property in the divisor-shift theorem below. -/
theorem roughHeadModulus_mem_smoothNumbers
    {W y : ℕ} (hWy : W ≤ y) :
    roughHeadModulus W ∈ Nat.smoothNumbers (y + 1) := by
  let P : Erdos390.Full.HeadPattern.Pattern := roughHeadZeroPattern W
  change P.modulus ∈ Nat.smoothNumbers (y + 1)
  apply modulus_mem_smoothNumbers P
  intro p hp
  change p ∈ primesUpTo W at hp
  exact (mem_primesUpTo.mp hp).2.trans hWy



/-- Exact inclusion--exclusion followed by the exact quotient-interval
reindexing for each head divisor. -/
theorem roughHeadFreeSmoothInterval_card_eq_divisorShift
    {W lo hi y : ℕ} (hWy : W ≤ y) :
    ((roughHeadFreeSmoothInterval W lo hi y).card : ℤ) =
      ∑ d ∈ (roughHeadModulus W).divisors,
        ArithmeticFunction.moebius d *
          (((smoothInterval (lo / d) (hi / d) y).card : ℕ) : ℤ) := by
  rw [roughHeadFreeSmoothInterval,
    roughHeadFree_card_eq_moebiusDivisorCounts]
  apply Finset.sum_congr rfl
  intro d hd
  have hdDvd : d ∣ roughHeadModulus W := (Nat.mem_divisors.mp hd).1
  have hdPos : 0 < d :=
    Nat.pos_of_dvd_of_pos hdDvd (roughHeadModulus_pos W)
  have hdSmooth : d ∈ Nat.smoothNumbers (y + 1) :=
    Nat.mem_smoothNumbers_of_dvd
      (roughHeadModulus_mem_smoothNumbers hWy) hdDvd
  rw [smooth_multiple_card_eq_quotient_interval hdPos hdSmooth]

/-- Real-cast form of the exact shifted smooth-interval identity. -/
theorem roughHeadFreeSmoothInterval_card_real_eq_divisorShift
    {W lo hi y : ℕ} (hWy : W ≤ y) :
    ((roughHeadFreeSmoothInterval W lo hi y).card : ℝ) =
      ∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          ((smoothInterval (lo / d) (hi / d) y).card : ℝ) := by
  have hZ := roughHeadFreeSmoothInterval_card_eq_divisorShift
    (W := W) (lo := lo) (hi := hi) (y := y) hWy
  have hR := congrArg (fun z : ℤ ↦ (z : ℝ)) hZ
  simpa only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] using hR







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughFixedHeadFriableShift -/
section


/-!
# The strongest available unconditional fixed-head friable shift

The paper uses the Hildebrand--Tenenbaum--Saias transition estimate to
obtain an `O_W(x / log(y)^2 + 1)` shift for a balanced physical block.
That transition estimate is not present in Mathlib, PrimeNumberTheoremAnd,
or the current project.  What *is* present is the closed uniform de Bruijn
estimate

`|Psi(X,y) - X * rho(log X / log y)| <= K * X / log y`

from `Full.FriableAsymptotic`.  This file records the strongest genuine
fixed-head consequence of that theorem.  It proves, without an analytic
hypothesis, an `O_W(X / log y + 1)` shift for the endpoint count, the
literal two-piece physical block, and its complete head Mobius closure.

The first lemma extends the already-proved floor-stability argument from
the recursive four-mark range `u <= 4` to the full endpoint range `u <= 5`.
It uses only the project's proved one-Lipschitz estimate for `rho`.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Full-range floor stability of the Dickman main term -/



/-! ## A fixed-divisor shift for the Dickman main term -/



/-! ## The closed fixed-head endpoint theorem -/



/-! ## Literal two-piece physical blocks -/





/-! ## Complete head Mobius closure at the available scale -/

/-- The inverse-divisor Mobius mass of the literal zero head is exactly its
reduced-residue density. -/
theorem roughHead_moebius_inv_sum_eq_density (W : ℕ) :
    (∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      roughHeadDensity W := by
  simpa only [roughHeadZeroPattern_modulus, roughHeadDensity] using
    Erdos390.Full.PaperScaleMarkedCell.sum_moebius_div_inv_eq_totient_ratio
      (roughHeadZeroPattern W)



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic -/
section


/-!
# Eventual raw broad-pool surplus on every active rough row

The tangent clean-list estimate is global in the common multiplier and
therefore cannot by itself give a lower bound in each complete rough row.
The rowwise input needed by the guard-capacity reduction is instead the
`active-clean-pool` estimate from Section 6 of the paper.  This file derives
that estimate from the already proved uniform de Bruijn bound and the
already proved fixed-head endpoint shift.

The proof has three quantitative layers.

* On a fixed-ratio interval `(A,B]`, the Dickman endpoint main term grows by
  a fixed positive multiple of `B-A`.  The uniform friable error is absorbed
  once `log y` is large.
* Exact head Möbius inversion and the fixed-divisor endpoint shift retain a
  fixed multiple of `A` in the head-free smooth interval.
* For an active label, `A = n / label` tends to infinity uniformly, while
  both `label / n` and `upperTailLength c n / n` tend to zero.  Consequently
  the broad pool dominates the literal upper-row quota and the three local
  guards.

The final theorem constructs
`RoughCanonicalActiveRawBroadSurplus ... 3 poolMinimum` for every fixed
`poolMinimum`, without a selector premise or an additional analytic
assumption.  The stronger linear real lower bound used to absorb that
constant is retained separately below.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells
open BankPaperRealization

noncomputable section

/-! ## A positive Dickman floor -/







/-! ## Growth of the unrestricted smooth interval -/





/-! ## Closing the fixed head -/

/-- Exact real identity for the rough-head Möbius density. -/
theorem roughHead_sum_moebius_div_eq_density (W : Nat) :
    (∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : Real) / (d : Real)) =
      roughHeadDensity W := by
  exact roughHead_moebius_inv_sum_eq_density W

/-- One fixed-divisor endpoint shift controls the corresponding smooth
interval after division by that head divisor. -/
theorem roughCanonical_smoothInterval_divisorShift_error
    {W : Nat} {Kshift : Real} {Y0 A B y d : Nat}
    (hshift : forall {X z e : Nat},
      Y0 <= z ->
      e ∈ (roughHeadModulus W).divisors -> e <= X ->
      Real.log (X : Real) <= 5 * Real.log (z : Real) ->
      |(FriableAsymptotic.friableCount (X / e) z : Real) -
          (FriableAsymptotic.friableCount X z : Real) / (e : Real)| <=
        Kshift * (X : Real) /
            ((e : Real) * Real.log (z : Real)) + 3)
    (hY : Y0 <= y) (hd : d ∈ (roughHeadModulus W).divisors)
    (hdA : d <= A) (hAB : A <= B)
    (hlogB : Real.log (B : Real) <= 5 * Real.log (y : Real)) :
    |((smoothInterval (A / d) (B / d) y).card : Real) -
        ((smoothInterval A B y).card : Real) / (d : Real)| <=
      Kshift * ((A : Real) + (B : Real)) /
          ((d : Real) * Real.log (y : Real)) + 6 := by
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hAPos : 0 < A := hdPos.trans_le hdA
  have hBPos : 0 < B := hAPos.trans_le hAB
  have hdB : d <= B := hdA.trans hAB
  have hlogA : Real.log (A : Real) <= 5 * Real.log (y : Real) := by
    have hmono : Real.log (A : Real) <= Real.log (B : Real) := by
      apply Real.log_le_log
      · exact_mod_cast hAPos
      · exact_mod_cast hAB
    exact hmono.trans hlogB
  have hAshift := hshift hY hd hdA hlogA
  have hBshift := hshift hY hd hdB hlogB
  have hmonoA := FriableAsymptotic.friableCount_mono_left (y := y) hAB
  have hdivAB : A / d <= B / d := Nat.div_le_div_right hAB
  have hmonoDiv :=
    FriableAsymptotic.friableCount_mono_left (y := y) hdivAB
  rw [smoothInterval_card_eq_psi_sub hdivAB,
    smoothInterval_card_eq_psi_sub hAB]
  simp_rw [Erdos390.Full.MarkedFriableAsymptotic.psi_eq_friableCount]
  rw [Nat.cast_sub hmonoDiv, Nat.cast_sub hmonoA]
  have hrearrange :
      ((FriableAsymptotic.friableCount (B / d) y : Real) -
          (FriableAsymptotic.friableCount (A / d) y : Real)) -
        ((FriableAsymptotic.friableCount B y : Real) -
          (FriableAsymptotic.friableCount A y : Real)) / (d : Real) =
      ((FriableAsymptotic.friableCount (B / d) y : Real) -
          (FriableAsymptotic.friableCount B y : Real) / (d : Real)) -
        ((FriableAsymptotic.friableCount (A / d) y : Real) -
          (FriableAsymptotic.friableCount A y : Real) / (d : Real)) := by
    ring
  rw [hrearrange]
  calc
    _ <=
        |(FriableAsymptotic.friableCount (B / d) y : Real) -
          (FriableAsymptotic.friableCount B y : Real) / (d : Real)| +
        |(FriableAsymptotic.friableCount (A / d) y : Real) -
          (FriableAsymptotic.friableCount A y : Real) / (d : Real)| :=
      abs_sub _ _
    _ <=
        (Kshift * (B : Real) /
            ((d : Real) * Real.log (y : Real)) + 3) +
        (Kshift * (A : Real) /
            ((d : Real) * Real.log (y : Real)) + 3) :=
      add_le_add hBshift hAshift
    _ = Kshift * ((A : Real) + (B : Real)) /
          ((d : Real) * Real.log (y : Real)) + 6 := by ring

/-- The exact Möbius closure differs from its positive density main term by
at most the sum of the fixed-divisor endpoint errors. -/
theorem roughCanonical_headFreeSmoothInterval_lower_of_shift
    {W : Nat} {Kshift : Real} {Y0 A B y : Nat}
    (hKshift : 0 < Kshift)
    (hshift : forall {X z d : Nat},
      Y0 <= z ->
      d ∈ (roughHeadModulus W).divisors -> d <= X ->
      Real.log (X : Real) <= 5 * Real.log (z : Real) ->
      |(FriableAsymptotic.friableCount (X / d) z : Real) -
          (FriableAsymptotic.friableCount X z : Real) / (d : Real)| <=
        Kshift * (X : Real) /
            ((d : Real) * Real.log (z : Real)) + 3)
    (hY : Y0 <= y) (hWy : W <= y) (hyTwo : 2 <= y)
    (hmodA : roughHeadModulus W <= A) (hAB : A <= B)
    (hlogB : Real.log (B : Real) <= 5 * Real.log (y : Real)) :
    roughHeadDensity W * ((smoothInterval A B y).card : Real) -
        (roughHeadModulus W : Real) *
          (Kshift * ((A : Real) + (B : Real)) /
              Real.log (y : Real) + 6) <=
      ((roughHeadFreeSmoothInterval W A B y).card : Real) := by
  let P := roughHeadModulus W
  let S : Real := ((smoothInterval A B y).card : Real)
  let E : Real :=
    Kshift * ((A : Real) + (B : Real)) / Real.log (y : Real) + 6
  have hPPos : 0 < P := by
    simpa only [P] using roughHeadModulus_pos W
  have hlogY : 0 < Real.log (y : Real) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hterm : ∀ d ∈ P.divisors,
      (ArithmeticFunction.moebius d : Real) * (S / (d : Real)) - E <=
        (ArithmeticFunction.moebius d : Real) *
          ((smoothInterval (A / d) (B / d) y).card : Real) := by
    intro d hd
    have hdP : d ∈ (roughHeadModulus W).divisors := by
      simpa only [P] using hd
    have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdLeP : d <= P := Nat.le_of_dvd hPPos
      (Nat.mem_divisors.mp hd).1
    have hdA : d <= A := hdLeP.trans (by simpa only [P] using hmodA)
    have herr := roughCanonical_smoothInterval_divisorShift_error
      (W := W) (Kshift := Kshift) (Y0 := Y0)
      hshift hY hdP hdA hAB hlogB
    have hdenomOne : (1 : Real) <= d := by exact_mod_cast hdPos
    have herr' :
        |((smoothInterval (A / d) (B / d) y).card : Real) -
            S / (d : Real)| <= E := by
      apply herr.trans
      dsimp only [E]
      have hdenom :
          (d : Real) * Real.log (y : Real) >=
            Real.log (y : Real) := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hdenomOne hlogY.le
      have hnumNonneg :
          0 <= Kshift * ((A : Real) + (B : Real)) :=
        mul_nonneg hKshift.le (by positivity)
      simpa only [add_comm] using
        add_le_add_right
          (div_le_div_of_nonneg_left
            hnumNonneg hlogY hdenom) 6
    have hmu : |(ArithmeticFunction.moebius d : Real)| <= 1 := by
      rcases ArithmeticFunction.moebius_eq_or d with hzero | hone | hneg
      · simp [hzero]
      · simp [hone]
      · simp [hneg]
    have hmul :
        |(ArithmeticFunction.moebius d : Real) *
            (((smoothInterval (A / d) (B / d) y).card : Real) -
              S / (d : Real))| <= E := by
      rw [abs_mul]
      exact (mul_le_mul hmu herr' (abs_nonneg _) zero_le_one).trans_eq
        (one_mul E)
    have hlower := (abs_le.mp hmul).1
    linarith
  rw [roughHeadFreeSmoothInterval_card_real_eq_divisorShift hWy]
  have hsum := Finset.sum_le_sum hterm
  have hmain :
      (∑ d ∈ P.divisors,
          ((ArithmeticFunction.moebius d : Real) * (S / (d : Real)) - E)) =
        roughHeadDensity W * S - (P.divisors.card : Real) * E := by
    calc
      _ = (∑ d ∈ P.divisors,
          (ArithmeticFunction.moebius d : Real) / (d : Real)) * S -
            (P.divisors.card : Real) * E := by
        rw [Finset.sum_sub_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d _hd
        ring
      _ = roughHeadDensity W * S - (P.divisors.card : Real) * E := by
        rw [show (∑ d ∈ P.divisors,
            (ArithmeticFunction.moebius d : Real) / (d : Real)) =
          roughHeadDensity W by
            simpa only [P] using roughHead_sum_moebius_div_eq_density W]
  rw [hmain] at hsum
  have hE : 0 <= E := by
    dsimp only [E]
    positivity
  have hcard : (P.divisors.card : Real) <= (P : Real) := by
    exact_mod_cast Nat.card_divisors_le_self P
  have hreplace :
      roughHeadDensity W * S - (P : Real) * E <=
        roughHeadDensity W * S - (P.divisors.card : Real) * E := by
    exact sub_le_sub_left (mul_le_mul_of_nonneg_right hcard hE) _
  simpa only [P, S, E] using hreplace.trans hsum



/-! ## Literal rough-row adapters -/













/-! ## Uniform paper-scale choices -/























end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_018 := by
  exact @Erdos390.WholePaper.roughCanonical_headFreeSmoothInterval_lower_of_shift
