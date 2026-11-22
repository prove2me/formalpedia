-- Prove2me | solution 1 for Erdos390.WholePaper.eventually_roughCanonicalActiveIntrinsicRawBroadSurplus_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:40:45.407666+00:00
-- url     : https://prove2.me/submissions/f953462b-6cf6-4293-abff-bac6e6bbd83a

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
import Definitions.Def_erdos390_analytic_foundations_007
import Theorems.Thm_Erdos390_WholePaper_eventually_roughCanonical_activeRawBroadPool_linear_lower_compact


section
theorem Erdos390.WholePaper.eventually_roughCanonical_activeRawBroadPool_linear_lower : Erdos390.RemainingAnalyticGoal008_008 := @Erdos390.WholePaper.eventually_roughCanonical_activeRawBroadPool_linear_lower_compact
end
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























end Pattern

end Erdos390.Full.HeadPattern

end

/- Source module: Erdos390.WholePaper.UpperScale -/
section


/-!
# Elementary scale facts for the upper bound

This module isolates the exact ceiling and endpoint used on the upper-bound
side of the paper.  Every asymptotic statement is proved directly from
elementary real-logarithm limits.  No prime-counting input is used.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section





/-- The elementary logarithmic comparison `log n / n → 0`, made public
for later upper-bound estimates. -/
theorem log_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

/-- The second-order scale `n / log n` diverges to infinity. -/
theorem secondOrderScale_tendsto_atTop :
    Tendsto secondOrderScale atTop atTop := by
  have hpos :
      ∀ᶠ n : ℕ in atTop,
        0 < Real.log (n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) (by positivity)
  have hright :
      Tendsto
        (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
        atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨log_natCast_div_natCast_tendsto_zero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  exact Eventually.of_forall fun n ↦ by
    change (Real.log (n : ℝ) / (n : ℝ))⁻¹ =
      secondOrderScale n
    rw [secondOrderScale, inv_div]

/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

/-- Eventually the second-order scale is strictly positive. -/
theorem eventually_secondOrderScale_pos :
    ∀ᶠ n : ℕ in atTop, 0 < secondOrderScale n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact secondOrderScale_pos hn

/-- The second-order scale is sublinear. -/
theorem secondOrderScale_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ secondOrderScale n / (n : ℝ))
      atTop (nhds 0) := by
  have hinvLog :
      Tendsto (fun n : ℕ ↦ 1 / Real.log (n : ℝ))
        atTop (nhds 0) := by
    simpa only [one_div] using
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  apply hinvLog.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [secondOrderScale]
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  have hlogNe : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp





/-- Ceiling changes `c n/log n` only by a negligible relative error. -/
theorem upperTailLength_normalized_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (upperTailLength c n : ℝ) / secondOrderScale n)
      atTop (nhds c) := by
  simpa only [upperTailLength] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hc.le).comp
      secondOrderScale_tendsto_atTop

/-- The chosen upper tail is `o(n)`. -/
theorem upperTailLength_ratio_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦ (upperTailLength c n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hmul :=
    (upperTailLength_normalized_tendsto hc).mul
      secondOrderScale_ratio_tendsto_zero
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_secondOrderScale_pos,
      eventually_gt_atTop 1] with n hscale hn
  have hscaleNe : secondOrderScale n ≠ 0 := hscale.ne'
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  field_simp





















end

end Erdos390.WholePaper

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



/-- The complete zero-head stratum has strictly positive density. -/
theorem roughHeadDensity_pos (W : ℕ) :
    0 < roughHeadDensity W := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot : (0 : ℝ) < ((roughHeadModulus W).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (roughHeadModulus_pos W)
  exact div_pos htot hmod



































/-! ## Exact head inclusion--exclusion and smooth physical shifts -/

















end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CompleteRoughDecomposition -/
section


/-!
# Complete rough/smooth decomposition

The complete rough label retains exactly the prime-power coordinates above
`y`.  This file defines the complementary literal quotient and proves that
the two pieces recover the original natural number, with exact complementary
factorizations and no auxiliary decomposition hypothesis.
-/

namespace Erdos390.WholePaper

noncomputable section



/-! ## Positivity, divisibility, and product recovery -/

/-- A complete rough label is always positive, including for `a = 0`, when
the empty factorization gives label `1`. -/
theorem completeRoughLabel_pos (y a : ℕ) :
    0 < completeRoughLabel y a := by
  rw [completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp

theorem completeRoughLabel_ne_zero (y a : ℕ) :
    completeRoughLabel y a ≠ 0 :=
  (completeRoughLabel_pos y a).ne'

/-- Literal Finsupp form of the high-prime factorization. -/
theorem completeRoughLabel_factorization_eq_filter_gt (y a : ℕ) :
    (completeRoughLabel y a).factorization =
      a.factorization.filter (fun p ↦ y < p) := by
  simpa only [completeRoughSignature] using
    completeRoughLabel_factorization y a



/-- The retained high-prime product is a literal divisor of the original
number. -/
theorem completeRoughLabel_dvd (y a : ℕ) :
    completeRoughLabel y a ∣ a := by
  by_cases ha : a = 0
  · rw [ha]
    exact dvd_zero _
  · rw [← Nat.factorization_le_iff_dvd
      (completeRoughLabel_ne_zero y a) ha,
      completeRoughLabel_factorization_eq_filter_gt]
    intro p
    rw [Finsupp.filter_apply]
    split_ifs <;> simp

/-- The requested multiplication direction: the original number is the
rough label times its literal complementary quotient. -/
theorem completeRough_decomposition (y a : ℕ) :
    a = completeRoughLabel y a * completeSmoothPart y a := by
  calc
    a = a / completeRoughLabel y a * completeRoughLabel y a :=
      (Nat.div_mul_cancel (completeRoughLabel_dvd y a)).symm
    _ = completeRoughLabel y a * (a / completeRoughLabel y a) :=
      Nat.mul_comm _ _
    _ = completeRoughLabel y a * completeSmoothPart y a := rfl



/-! ## The complementary low-prime factorization -/

/-- The quotient retains exactly the complementary coordinates `p ≤ y`. -/
theorem completeSmoothPart_factorization_eq_filter_le (y a : ℕ) :
    (completeSmoothPart y a).factorization =
      a.factorization.filter (fun p ↦ p ≤ y) := by
  rw [completeSmoothPart,
    Nat.factorization_div (completeRoughLabel_dvd y a),
    completeRoughLabel_factorization_eq_filter_gt]
  ext p
  simp only [Finsupp.filter_apply]
  by_cases hpLow : p ≤ y
  · have hpNotHigh : ¬y < p := Nat.not_lt_of_ge hpLow
    simp [hpLow, hpNotHigh]
  · have hpHigh : y < p := Nat.lt_of_not_ge hpLow
    simp [hpLow, hpHigh]

/-- Coordinate form of the exact low-prime factorization. -/
theorem completeSmoothPart_factorization_apply (y a p : ℕ) :
    (completeSmoothPart y a).factorization p =
      if p ≤ y then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeSmoothPart_factorization_eq_filter_le y a)
  simpa only [Finsupp.filter_apply] using h



/-- Nonzero smooth-part coordinates lie weakly below the cutoff. -/
theorem completeSmoothPart_factorization_support
    {y a p : ℕ}
    (hp : (completeSmoothPart y a).factorization p ≠ 0) :
    p ≤ y := by
  rw [completeSmoothPart_factorization_apply] at hp
  by_contra hpLow
  simp [hpLow] at hp



/-- For a positive original number, the complementary quotient is positive. -/
theorem completeSmoothPart_pos {y a : ℕ} (ha : 0 < a) :
    0 < completeSmoothPart y a := by
  rw [completeSmoothPart]
  apply Nat.div_pos
  · exact Nat.le_of_dvd ha (completeRoughLabel_dvd y a)
  · exact completeRoughLabel_pos y a

/-- For a positive original number, the complementary quotient is literally
`(y+1)`-smooth in Mathlib's positive-number convention. -/
theorem completeSmoothPart_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeSmoothPart y a ∈ Nat.smoothNumbers (y + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpDvd
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeSmoothPart_pos ha).ne' hpDvd
  have hpLow : p ≤ y :=
    completeSmoothPart_factorization_support hfactorPos.ne'
  omega

/-! ## Uniqueness and the smooth-label criterion -/

/-- Uniqueness of the decomposition under the literal complementary
factorization-support conditions. -/
theorem completeRoughDecomposition_unique
    {y a rough smooth : ℕ}
    (hrough : rough ≠ 0) (hsmooth : smooth ≠ 0)
    (hproduct : a = rough * smooth)
    (hroughSupport : ∀ p, rough.factorization p ≠ 0 → y < p)
    (hsmoothSupport : ∀ p, smooth.factorization p ≠ 0 → p ≤ y) :
    rough = completeRoughLabel y a ∧
      smooth = completeSmoothPart y a := by
  have hfactorization :
      a.factorization = rough.factorization + smooth.factorization := by
    rw [hproduct, Nat.factorization_mul hrough hsmooth]
  have hroughEq : rough = completeRoughLabel y a := by
    apply Nat.eq_of_factorization_eq' hrough
      (completeRoughLabel_ne_zero y a)
    rw [completeRoughLabel_factorization_eq_filter_gt]
    ext p
    have hcoordinate :=
      congrArg (fun f : ℕ →₀ ℕ ↦ f p) hfactorization
    simp only [Finsupp.add_apply] at hcoordinate
    rw [Finsupp.filter_apply]
    by_cases hpHigh : y < p
    · rw [if_pos hpHigh]
      have hsmoothZero : smooth.factorization p = 0 := by
        by_contra hsmoothNonzero
        exact (Nat.not_le_of_gt hpHigh)
          (hsmoothSupport p hsmoothNonzero)
      simpa only [hsmoothZero, add_zero] using hcoordinate.symm
    · rw [if_neg hpHigh]
      by_contra hroughNonzero
      exact hpHigh (hroughSupport p hroughNonzero)
  refine ⟨hroughEq, ?_⟩
  apply Nat.mul_left_cancel (completeRoughLabel_pos y a)
  calc
    completeRoughLabel y a * smooth = rough * smooth := by
      rw [hroughEq]
    _ = a := hproduct.symm
    _ = completeRoughLabel y a * completeSmoothPart y a :=
      completeRough_decomposition y a





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasCanonicalRowBridge -/
section


/-!
# Canonical-row consumer for the weighted Saias block

The analytic four-endpoint expression is useful to the construction only
after it is tied back to the literal complete-rough row used by floating
rounding.  This file supplies that consumer-facing bridge.  The sum over a
canonical `rowSet` is identified unconditionally with the already-defined
literal raw row mass.  The upper quota minus that mass is then connected to
`roughPhysicalFriableCombination` and hence to the weighted Saias bound.

The upper endpoint identification is an exact equality.  Finite head
inclusion--exclusion and the fixed-head physical shift occur between the
literal raw mass and the density-scaled four-endpoint block in the paper,
so their error is retained as a separate explicit allowance.  It is not
silently folded into the HT--Saias hypothesis.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section









/-- Multiplying an intrinsic complete-rough label by a positive smooth
integer leaves that complete rough label unchanged. -/
theorem completeRoughLabel_mul_eq_of_isCompleteRoughLabel_of_smooth
    {y label s : ℕ}
    (hlabel : IsCompleteRoughLabel y label)
    (hs : s ∈ Nat.smoothNumbers (y + 1)) :
    completeRoughLabel y (label * s) = label := by
  have hsPos : 0 < s :=
    (Nat.mem_smoothNumbers.mp hs).1.bot_lt
  have hsSupport : ∀ p, s.factorization p ≠ 0 → p ≤ y := by
    intro p hp
    have hpPrime : p.Prime := by
      by_contra hnotPrime
      rw [Nat.factorization_eq_zero_of_not_prime s hnotPrime] at hp
      exact hp rfl
    have hpDvd : p ∣ s := Nat.dvd_of_factorization_pos hp
    have hpLt := (Nat.mem_smoothNumbers').mp hs p hpPrime hpDvd
    omega
  have hunique := completeRoughDecomposition_unique
    (y := y) (a := label * s) (rough := label) (smooth := s)
      hlabel.1.ne' hsPos.ne' rfl hlabel.2 hsSupport
  exact hunique.1.symm

/-- Exact row-to-smooth-quotient reindexing on an arbitrary natural
half-open interval. -/
theorem completeRoughRowFiber_Ioc_card_eq_smoothInterval
    {lo hi y label : ℕ} (hlabel : IsCompleteRoughLabel y label) :
    (completeRoughRowFiber y (Finset.Ioc lo hi) label).card =
      (Erdos390.Full.StructuredCells.smoothInterval
        (lo / label) (hi / label) y).card := by
  apply Finset.card_bij (fun a _ha ↦ a / label)
  · intro a ha
    rw [mem_completeRoughRowFiber] at ha
    have haInterval := Finset.mem_Ioc.mp ha.1
    have hdvd : label ∣ a := by
      rw [← ha.2]
      exact completeRoughLabel_dvd y a
    apply Erdos390.Full.StructuredCells.mem_smoothInterval.mpr
    constructor
    · apply (Nat.div_lt_iff_lt_mul hlabel.1).mpr
      simpa [Nat.div_mul_cancel hdvd] using haInterval.1
    · constructor
      · apply (Nat.le_div_iff_mul_le hlabel.1).mpr
        simpa [Nat.div_mul_cancel hdvd] using haInterval.2
      · have haPos : 0 < a := Nat.zero_lt_of_lt haInterval.1
        simpa only [completeSmoothPart, ha.2] using
          completeSmoothPart_mem_smoothNumbers (y := y) haPos
  · intro a₁ ha₁ a₂ ha₂ heq
    rw [mem_completeRoughRowFiber] at ha₁ ha₂
    have hdvd₁ : label ∣ a₁ := by
      rw [← ha₁.2]
      exact completeRoughLabel_dvd y a₁
    have hdvd₂ : label ∣ a₂ := by
      rw [← ha₂.2]
      exact completeRoughLabel_dvd y a₂
    calc
      a₁ = a₁ / label * label := (Nat.div_mul_cancel hdvd₁).symm
      _ = a₂ / label * label := by rw [heq]
      _ = a₂ := Nat.div_mul_cancel hdvd₂
  · intro s hs
    have hsData :=
      Erdos390.Full.StructuredCells.mem_smoothInterval.mp hs
    refine ⟨label * s, ?_, ?_⟩
    · apply mem_completeRoughRowFiber.mpr
      constructor
      · apply Finset.mem_Ioc.mpr
        constructor
        · have hlo := (Nat.div_lt_iff_lt_mul hlabel.1).mp hsData.1
          simpa only [Nat.mul_comm] using hlo
        · have hhi := (Nat.le_div_iff_mul_le hlabel.1).mp hsData.2.1
          simpa only [Nat.mul_comm] using hhi
      · exact completeRoughLabel_mul_eq_of_isCompleteRoughLabel_of_smooth
          hlabel hsData.2.2
    · simpa only [Nat.mul_comm] using Nat.mul_div_left s hlabel.1





































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



/-- The fixed Dickman floor is strictly positive. -/
theorem roughCanonicalPoolDickmanFloor_pos :
    0 < roughCanonicalPoolDickmanFloor := by
  unfold roughCanonicalPoolDickmanFloor
  exact rho_pos_on_zero_five (by norm_num) le_rfl



/-! ## Growth of the unrestricted smooth interval -/





/-! ## Closing the fixed head -/









/-! ## Literal rough-row adapters -/



/-- The retained raw broad-pool density is strictly positive. -/
theorem roughCanonicalRawBroadPoolDensity_pos (W : Nat) :
    0 < roughCanonicalRawBroadPoolDensity W := by
  unfold roughCanonicalRawBroadPoolDensity
  exact div_pos
    (mul_pos (roughHeadDensity_pos W)
      roughCanonicalPoolDickmanFloor_pos) (by norm_num)





/-- The literal upper-row target is bounded by its quotient interval
length, hence by `h / label + 1`. -/
theorem roughUpperCompleteRoughRowTarget_le_div_add_one
    {n h y label : Nat} (hlabel : IsCompleteRoughLabel y label) :
    roughUpperCompleteRoughRowTarget n h y label <= h / label + 1 := by
  have hlabelPos := hlabel.1
  have hsubset :
      smoothInterval ((2 * n) / label) ((2 * n + h) / label) y ⊆
        Finset.Ioc ((2 * n) / label) ((2 * n + h) / label) := by
    intro a ha
    exact Finset.mem_Ioc.mpr
      ⟨(mem_smoothInterval.mp ha).1, (mem_smoothInterval.mp ha).2.1⟩
  unfold roughUpperCompleteRoughRowTarget roughUpperBlock
  rw [completeRoughRowFiber_Ioc_card_eq_smoothInterval hlabel]
  have hcard := Finset.card_le_card hsubset
  have hquotient :
      (2 * n + h) / label <=
        (2 * n) / label + h / label + 1 := by
    rw [Nat.add_div hlabelPos]
    split_ifs <;> omega
  have hlength :
      (2 * n + h) / label - (2 * n) / label <= h / label + 1 := by
    apply Nat.sub_le_iff_le_add'.mpr
    simpa only [Nat.add_assoc] using hquotient
  have hcard' :
      (smoothInterval ((2 * n) / label) ((2 * n + h) / label) y).card <=
        (2 * n + h) / label - (2 * n) / label := by
    simpa only [Nat.card_Ioc] using hcard
  exact hcard'.trans hlength



/-! ## Uniform paper-scale choices -/





private theorem roughCanonical_rpow_tendsto_atTop
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => (n : Real) ^ deltaStar) atTop atTop := by
  exact (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop

/-- Active labels have uniformly large natural quotient scale once the
real exceptional cutoff is large. -/
theorem roughCanonical_activeLabel_div_scale_lower
    {n label A0 : Nat} {deltaStar : Real}
    (_hn : 0 < n) (hlabel : 0 < label)
    (hactive : (n : Real) ^ deltaStar <=
      2 * (n : Real) / (label : Real))
    (hpower : (2 * (A0 + 1) : Real) <= (n : Real) ^ deltaStar) :
    A0 <= n / label := by
  have hlabelReal : (0 : Real) < label := by exact_mod_cast hlabel
  have hquotient : (n : Real) ^ deltaStar / 2 <=
      (n : Real) / (label : Real) := by
    apply (div_le_iff₀ (by norm_num : (0 : Real) < 2)).2
    calc
      (n : Real) ^ deltaStar <=
          2 * (n : Real) / (label : Real) := hactive
      _ = (n : Real) / (label : Real) * 2 := by ring
  have hnatUpper :
      (n : Real) / (label : Real) < ((n / label : Nat) : Real) + 1 := by
    apply (div_lt_iff₀ hlabelReal).2
    have hnat := (Nat.div_lt_iff_lt_mul hlabel).mp
      (Nat.lt_succ_self (n / label))
    exact_mod_cast hnat
  have hA0 : (A0 : Real) + 1 <= (n : Real) ^ deltaStar / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : Real) < 2)).2
    calc
      ((A0 : Real) + 1) * 2 =
          2 * ((A0 : Real) + 1) := by ring
      _ <= (n : Real) ^ deltaStar := hpower
  have hreal :
      (A0 : Real) + 1 < ((n / label : Nat) : Real) + 1 :=
    lt_of_le_of_lt hA0 (hquotient.trans_lt hnatUpper)
  have hnat : A0 + 1 < n / label + 1 := by exact_mod_cast hreal
  omega







/-- Eventually, every intrinsic active row has enough raw broad coordinates
for its full upper-row target, any prescribed fixed correction-pool
minimum, and the literal three-coordinate guard budget. -/
theorem eventually_roughCanonicalActiveIntrinsicRawBroadSurplus
    (W K poolMinimum : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      RoughCanonicalActiveIntrinsicRawBroadSurplus W n
        (upperTailLength c n) K 3 poolMinimum deltaStar := by
  have hlinear :=
    eventually_roughCanonical_activeRawBroadPool_linear_lower
      W K hc hdelta
  let density := roughCanonicalRawBroadPoolDensity W
  have hdensity : 0 < density := by
    dsimp only [density]
    exact roughCanonicalRawBroadPoolDensity_pos W
  have htailSmall : ∀ᶠ n : Nat in atTop,
      (upperTailLength c n : Real) / (n : Real) <= density / 4 := by
    have hT := upperTailLength_ratio_tendsto_zero hc
    have hsmall := hT.eventually
      (eventually_lt_nhds (div_pos hdensity (by norm_num : (0 : Real) < 4)))
    filter_upwards [hsmall] with n hn
    exact hn.le
  let constantTarget : Nat := max 4 (poolMinimum + 3)
  let A0 : Nat := max 1 ⌈(2 * (constantTarget : Real)) / density⌉₊
  have hpowerEvent : ∀ᶠ n : Nat in atTop,
      (2 * (A0 + 1) : Real) <= (n : Real) ^ deltaStar :=
    (roughCanonical_rpow_tendsto_atTop hdelta).eventually
      (eventually_ge_atTop (2 * (A0 + 1) : Real))
  filter_upwards [eventually_gt_atTop 0, hlinear, htailSmall, hpowerEvent]
    with n hn hlinearN htail hpower
  unfold RoughCanonicalActiveIntrinsicRawBroadSurplus
  intro label hlabelData hactive
  have hlabelPos : 0 < label := hlabelData.1
  let A := n / label
  have hA0 : A0 <= A :=
    roughCanonical_activeLabel_div_scale_lower hn hlabelPos hactive.2 hpower
  have hAOne : 1 <= A := (le_max_left 1 _).trans hA0
  have hlinearRow : density * (A : Real) <=
      (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
        (yNat n) label).card := by
    simpa only [density, A] using
      hlinearN label hlabelData hactive
  have htarget :
      roughUpperCompleteRoughRowTarget n (upperTailLength c n)
          (yNat n) label <= upperTailLength c n / label + 1 := by
    exact roughUpperCompleteRoughRowTarget_le_div_add_one
      hlabelData
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  have hlabelReal : (0 : Real) < label := by exact_mod_cast hlabelPos
  have hARealUpper : (n : Real) / (label : Real) < (A : Real) + 1 := by
    apply (div_lt_iff₀ hlabelReal).2
    have hnat := (Nat.div_lt_iff_lt_mul hlabelPos).mp
      (Nat.lt_succ_self A)
    exact_mod_cast hnat
  have htailDiv :
      (upperTailLength c n : Real) / (label : Real) <=
        density / 4 * ((A : Real) + 1) := by
    calc
      (upperTailLength c n : Real) / (label : Real) =
          ((upperTailLength c n : Real) / (n : Real)) *
            ((n : Real) / (label : Real)) := by
        field_simp [hnReal.ne', hlabelReal.ne']
      _ <= density / 4 * ((n : Real) / (label : Real)) := by
        exact mul_le_mul_of_nonneg_right htail
          (div_nonneg hnReal.le hlabelReal.le)
      _ <= density / 4 * ((A : Real) + 1) := by
        exact mul_le_mul_of_nonneg_left hARealUpper.le
          (div_nonneg hdensity.le (by norm_num))
  have htailDiv' :
      ((upperTailLength c n / label : Nat) : Real) <=
        density / 2 * (A : Real) := by
    have hcastDiv :
        ((upperTailLength c n / label : Nat) : Real) <=
          (upperTailLength c n : Real) / (label : Real) := Nat.cast_div_le
    have hAOneReal : (1 : Real) <= A := by exact_mod_cast hAOne
    calc
      ((upperTailLength c n / label : Nat) : Real) <=
          (upperTailLength c n : Real) / (label : Real) := hcastDiv
      _ <= density / 4 * ((A : Real) + 1) := htailDiv
      _ <= density / 4 * (2 * (A : Real)) := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        exact div_nonneg hdensity.le (by norm_num)
      _ = density / 2 * (A : Real) := by ring
  have hconstant : (constantTarget : Real) <=
      density / 2 * (A : Real) := by
    have hceil : (2 * (constantTarget : Real)) / density <=
        (⌈(2 * (constantTarget : Real)) / density⌉₊ : Real) :=
      Nat.le_ceil _
    have hceilA :
        (⌈(2 * (constantTarget : Real)) / density⌉₊ : Nat) <= A :=
      (le_max_right 1 _).trans hA0
    have hA : (2 * (constantTarget : Real)) / density <= (A : Real) :=
      hceil.trans (by exact_mod_cast hceilA)
    have := (div_le_iff₀ hdensity).1 hA
    nlinarith
  have hfourTargetNat : 4 <= constantTarget := by
    exact le_max_left 4 (poolMinimum + 3)
  have hminimumTargetNat : poolMinimum + 3 <= constantTarget := by
    exact le_max_right 4 (poolMinimum + 3)
  have hfourTargetCast : (4 : Real) <= (constantTarget : Real) := by
    exact_mod_cast hfourTargetNat
  have hminimumTargetCast : ((poolMinimum + 3 : Nat) : Real) <=
      (constantTarget : Real) := by
    exact_mod_cast hminimumTargetNat
  have hfour : (4 : Real) <= density / 2 * (A : Real) :=
    hfourTargetCast.trans hconstant
  have hminimumConstant : ((poolMinimum + 3 : Nat) : Real) <=
      density / 2 * (A : Real) :=
    hminimumTargetCast.trans hconstant
  have htargetPool :
      roughUpperCompleteRoughRowTarget n (upperTailLength c n)
          (yNat n) label + 3 <=
        (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
          (yNat n) label).card := by
    have htargetReal :
        (roughUpperCompleteRoughRowTarget n (upperTailLength c n)
            (yNat n) label + 3 : Nat) <=
          density * (A : Real) := by
      push_cast
      have htargetCast :
          (roughUpperCompleteRoughRowTarget n (upperTailLength c n)
              (yNat n) label : Real) <=
            ((upperTailLength c n / label : Nat) : Real) + 1 := by
        exact_mod_cast htarget
      linarith [hfour]
    exact_mod_cast htargetReal.trans hlinearRow
  have hminimumPool : poolMinimum + 3 <=
      (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
        (yNat n) label).card := by
    have hreal : ((poolMinimum + 3 : Nat) : Real) <=
        (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
          (yNat n) label).card := by
      have hhalf : density / 2 * (A : Real) <= density * (A : Real) := by
        have hAReal : (0 : Real) <= A := Nat.cast_nonneg A
        exact mul_le_mul_of_nonneg_right (by linarith) hAReal
      exact hminimumConstant.trans (hhalf.trans hlinearRow)
    exact_mod_cast hreal
  by_cases hminimumLeTarget : poolMinimum <=
      roughUpperCompleteRoughRowTarget n (upperTailLength c n)
        (yNat n) label
  · rw [max_eq_right hminimumLeTarget]
    exact htargetPool
  · rw [max_eq_left (le_of_not_ge hminimumLeTarget)]
    exact hminimumPool







end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_006 := by
  exact @Erdos390.WholePaper.eventually_roughCanonicalActiveIntrinsicRawBroadSurplus
