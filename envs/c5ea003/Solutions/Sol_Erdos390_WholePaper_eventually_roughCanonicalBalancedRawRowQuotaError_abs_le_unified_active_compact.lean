-- Prove2me | solution 1 for Erdos390.WholePaper.eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:51:28.960848+00:00
-- url     : https://prove2.me/submissions/0334d0dc-5c18-49c3-9163-c38cf629826a

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
import Definitions.Def_erdos390_analytic_foundations_008
import Definitions.Def_erdos390_analytic_foundations_009
import Theorems.Thm_Erdos390_WholePaper_abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq_compact
import Theorems.Thm_Erdos390_WholePaper_roughCanonicalBalancedDickmanTransitionLedger_le_compact
import Theorems.Thm_Erdos390_WholePaper_roughCanonicalBalancedSaiasTransitionBudget_le_compact
import Theorems.Thm_Erdos390_WholePaper_roughCanonicalBalancedSharpFixedHeadBudget_le_compact
import Theorems.Thm_Erdos390_WholePaper_roughCompactBV_translation_le_of_le_compact
import Theorems.Thm_Erdos390_WholePaper_roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation_compact
import Theorems.Thm_Erdos390_WholePaper_roughFriableMain_abs_le_with_balanceError_compact
import Theorems.Thm_Erdos390_WholePaper_roughSaiasDickmanCorrection_difference_abs_le_compact
import Theorems.Thm_Erdos390_WholePaper_roughSaiasIntervalFixedDivisorShiftBudget_sharp_le_compact
import Theorems.Thm_Erdos390_WholePaper_roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect_compact
import Theorems.Thm_Erdos390_WholePaper_roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq_compact
import Theorems.Thm_Erdos390_WholePaper_sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq_compact













section
theorem Erdos390.WholePaper.sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq : Erdos390.RemainingAnalyticGoal008_036 := @Erdos390.WholePaper.sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq_compact
end
section
theorem Erdos390.WholePaper.roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq : Erdos390.RemainingAnalyticGoal008_031 := @Erdos390.WholePaper.roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq_compact
end
section
theorem Erdos390.WholePaper.roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect : Erdos390.RemainingAnalyticGoal008_029 := @Erdos390.WholePaper.roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect_compact
end
section
theorem Erdos390.WholePaper.roughSaiasIntervalFixedDivisorShiftBudget_sharp_le : Erdos390.RemainingAnalyticGoal008_028 := @Erdos390.WholePaper.roughSaiasIntervalFixedDivisorShiftBudget_sharp_le_compact
end
section
theorem Erdos390.WholePaper.roughSaiasDickmanCorrection_difference_abs_le : Erdos390.RemainingAnalyticGoal008_026 := @Erdos390.WholePaper.roughSaiasDickmanCorrection_difference_abs_le_compact
end
section
universe u_1
theorem Erdos390.WholePaper.roughFriableMain_abs_le_with_balanceError : Erdos390.RemainingAnalyticGoal008_022.{u_1} := @Erdos390.WholePaper.roughFriableMain_abs_le_with_balanceError_compact
end
section
theorem Erdos390.WholePaper.roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation : Erdos390.RemainingAnalyticGoal008_021 := @Erdos390.WholePaper.roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation_compact
end
section
theorem Erdos390.WholePaper.roughCompactBV_translation_le_of_le : Erdos390.RemainingAnalyticGoal008_019 := @Erdos390.WholePaper.roughCompactBV_translation_le_of_le_compact
end
section
theorem Erdos390.WholePaper.roughCanonicalBalancedSharpFixedHeadBudget_le : Erdos390.RemainingAnalyticGoal008_016 := @Erdos390.WholePaper.roughCanonicalBalancedSharpFixedHeadBudget_le_compact
end
section
theorem Erdos390.WholePaper.roughCanonicalBalancedSaiasTransitionBudget_le : Erdos390.RemainingAnalyticGoal008_015 := @Erdos390.WholePaper.roughCanonicalBalancedSaiasTransitionBudget_le_compact
end
section
theorem Erdos390.WholePaper.roughCanonicalBalancedDickmanTransitionLedger_le : Erdos390.RemainingAnalyticGoal008_014 := @Erdos390.WholePaper.roughCanonicalBalancedDickmanTransitionLedger_le_compact
end
section
theorem Erdos390.WholePaper.abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq : Erdos390.RemainingAnalyticGoal008_002 := @Erdos390.WholePaper.abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq_compact
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











/-- The continuous Dickman test weight is continuous away from the two
irrelevant singular points `0` and `1`. -/
theorem continuousOn_dickmanContinuousWeight (X : ℝ) :
    ContinuousOn (dickmanContinuousWeight X) (Set.Ioi (1 : ℝ)) := by
  intro t ht
  rw [Set.mem_Ioi] at ht
  have ht0 : t ≠ 0 := by linarith [ht]
  have ht1 : t ≠ 1 := by linarith [ht]
  have hlog_ne : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht]) ht1
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0
  have hq : ContinuousAt
      (fun u : ℝ => Real.log X / Real.log u - 1) t :=
    (continuousAt_const.div hlog hlog_ne).sub continuousAt_const
  have hrho : ContinuousAt
      (fun u : ℝ => rho (Real.log X / Real.log u - 1)) t :=
    continuous_rho.continuousAt.comp hq
  have hmain : ContinuousAt
      (fun u : ℝ => X / u * rho (Real.log X / Real.log u - 1)) t :=
    (continuousAt_const.div continuousAt_id ht0).mul hrho
  exact (hmain.div hlog hlog_ne).continuousWithinAt

/-- Pointwise derivative identity behind the de Bruijn integral. -/
theorem hasDerivAt_dickmanAntiderivative (X t : ℝ) (ht : 1 < t)
    (hq1 : 1 < Real.log X / Real.log t)
    (hq6 : Real.log X / Real.log t ≤ 6) :
    HasDerivAt (dickmanAntiderivative X)
      (dickmanContinuousWeight X t) t := by
  have ht0 : t ≠ 0 := by linarith
  have htlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  let q : ℝ → ℝ := fun s => Real.log X / Real.log s
  have hq : HasDerivAt q
      (-(Real.log X) / (t * (Real.log t) ^ 2)) t := by
    have hraw := (hasDerivAt_const t (Real.log X)).div
      (Real.hasDerivAt_log ht0) htlog
    convert hraw using 1
    field_simp
    ring
  have hrho := (hasDerivAt_rho hq1 hq6).comp t hq
  have hmul := (hasDerivAt_const t X).mul hrho
  convert hmul using 1
  unfold dickmanContinuousWeight
  dsimp [q] at hmul ⊢
  have hq0 : Real.log X / Real.log t ≠ 0 := by linarith
  have hlogX : Real.log X ≠ 0 := by
    intro hzero
    apply hq0
    rw [hzero, zero_div]
  field_simp [hlogX, htlog, ht0]
  ring

/-- Exact evaluation of the continuous de Bruijn integral by the Dickman
delay equation.  The compact coordinate condition is stated explicitly and
is elementary to verify in each method-of-steps strip. -/
theorem integral_dickmanContinuousWeight (X z y : ℝ)
    (hz : 1 < z) (hzy : z ≤ y)
    (hq : ∀ t ∈ Set.Icc z y,
      1 < Real.log X / Real.log t ∧
        Real.log X / Real.log t ≤ 6) :
    (∫ t in z..y, dickmanContinuousWeight X t) =
      dickmanAntiderivative X y - dickmanAntiderivative X z := by
  have hcontW : ContinuousOn
      (dickmanContinuousWeight X) (Set.Icc z y) :=
    (continuousOn_dickmanContinuousWeight X).mono (fun t ht => by
      rw [Set.mem_Ioi]
      exact hz.trans_le ht.1)
  have hint : IntervalIntegrable (dickmanContinuousWeight X)
      MeasureTheory.volume z y := by
    rw [← Set.uIcc_of_le hzy] at hcontW
    exact hcontW.intervalIntegrable
  have hcontA : ContinuousOn
      (dickmanAntiderivative X) (Set.Icc z y) := by
    intro t ht
    exact (hasDerivAt_dickmanAntiderivative X t
      (hz.trans_le ht.1) (hq t ht).1 (hq t ht).2).continuousAt.continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hzy hcontA
  · intro t ht
    exact hasDerivAt_dickmanAntiderivative X t (hz.trans ht.1)
      (hq t ⟨ht.1.le, ht.2.le⟩).1
      (hq t ⟨ht.1.le, ht.2.le⟩).2
  · exact hint









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







































/-- The Dickman integral remains valid when the upper endpoint lies on the
birth face `u = 1`; differentiability is only needed in the open interval. -/
theorem integral_dickmanContinuousWeight_closed_top (X z y : ℝ)
    (hz : 1 < z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc z y,
      1 ≤ Real.log X / Real.log t ∧
        Real.log X / Real.log t ≤ 6) :
    (∫ t in z..y, dickmanContinuousWeight X t) =
      dickmanAntiderivative X y - dickmanAntiderivative X z := by
  have hcontW : ContinuousOn
      (dickmanContinuousWeight X) (Set.Icc z y) :=
    (continuousOn_dickmanContinuousWeight X).mono (fun t ht => by
      rw [Set.mem_Ioi]
      exact hz.trans_le ht.1)
  have hint : IntervalIntegrable (dickmanContinuousWeight X)
      MeasureTheory.volume z y := by
    rw [← Set.uIcc_of_le hzy.le] at hcontW
    exact hcontW.intervalIntegrable
  have hcontA : ContinuousOn
      (dickmanAntiderivative X) (Set.Icc z y) := by
    intro t ht
    have ht1 : 1 < t := hz.trans_le ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlogne : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    have hqcont : ContinuousAt (fun s : ℝ => Real.log X / Real.log s) t :=
      continuousAt_const.div (Real.continuousAt_log ht0) hlogne
    exact (continuousAt_const.mul
      (continuous_rho.continuousAt.comp hqcont)).continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hzy.le hcontA
  · intro t ht
    have htI : t ∈ Set.Icc z y := ⟨ht.1.le, ht.2.le⟩
    have hqt6 := (hq t htI).2
    have hlogt : 0 < Real.log t := Real.log_pos (hz.trans ht.1)
    have hlogy : 0 < Real.log y := Real.log_pos (hz.trans hzy)
    have hlogty : Real.log t < Real.log y :=
      Real.strictMonoOn_log (show t ∈ Set.Ioi 0 by
        exact hz.trans ht.1 |>.trans' (by norm_num))
        (show y ∈ Set.Ioi 0 by exact hz.trans hzy |>.trans' (by norm_num)) ht.2
    have hqy1 := (hq y ⟨hzy.le, le_rfl⟩).1
    have hlogX : 0 < Real.log X := by
      have h := (le_div_iff₀ hlogy).mp hqy1
      linarith
    have hqstrict : 1 < Real.log X / Real.log t := by
      have hdiv : Real.log X / Real.log y < Real.log X / Real.log t := by
        exact (div_lt_div_iff_of_pos_left hlogX hlogy hlogt).2 hlogty
      exact hqy1.trans_lt hdiv
    exact hasDerivAt_dickmanAntiderivative X t (hz.trans ht.1)
      hqstrict hqt6
  · exact hint














/-- The integral cutoff `floor(n^(2/9))` retains enough logarithmic size
for the complete four-mark coordinate range. -/
theorem eventually_one_fifth_L_le_log_yNat :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ) := by
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0,
    hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually
      (Filter.eventually_ge_atTop (45 * Real.log 2))] with n hn hyn hLn
  have hypos : 0 < y n := y_pos hn
  have hyNatLower : y n / 2 ≤ (yNat n : ℝ) := by
    have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogLower : Real.log (y n / 2) ≤ Real.log (yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    (1 / 5 : ℝ) * L n ≤ Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      linarith
    _ ≤ Real.log (yNat n : ℝ) := hlogLower






end Erdos390.Full.FriableAsymptotic

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

/-- For `c > 0`, the integral tail length itself diverges. -/
theorem upperTailLength_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (upperTailLength c) atTop atTop := by
  have hscaled :
      Tendsto (fun n : ℕ ↦ c * secondOrderScale n) atTop atTop :=
    secondOrderScale_tendsto_atTop.const_mul_atTop hc
  simpa only [upperTailLength] using
    (tendsto_nat_ceil_atTop (α := ℝ)).comp hscaled

/-- For `c > 0`, the integral tail is eventually nonempty. -/
theorem eventually_upperTailLength_pos {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 < upperTailLength c n :=
  (upperTailLength_tendsto_atTop hc).eventually (eventually_gt_atTop 0)

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





/-- Literal physical-shift identity: finite head inclusion--exclusion
turns the head-free physical block into the signed sum of unrestricted
blocks with every endpoint divided by the same head divisor. -/
theorem roughHeadFreeSmoothPhysicalBlock_eq_divisorShift
    {W lo split hi y : ℕ} {α broad : ℝ}
    (hWy : W ≤ y) :
    roughHeadFreeSmoothPhysicalBlock W lo split hi y α broad =
      ∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
            α broad := by
  rw [roughHeadFreeSmoothPhysicalBlock,
    roughHeadFreeSmoothInterval_card_real_eq_divisorShift
      (W := W) (lo := split) (hi := hi) (y := y) hWy,
    roughHeadFreeSmoothInterval_card_real_eq_divisorShift
      (W := W) (lo := lo) (hi := split) (y := y) hWy,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [roughSmoothPhysicalBlock]
  ring

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

/-- Rewrite the literal smooth physical block as a three-endpoint
combination of the genuine friable counting function. -/
theorem roughSmoothPhysicalBlock_eq_friableEndpoints
    {lo split hi y : ℕ} {alpha broad : ℝ}
    (hloSplit : lo ≤ split) (hSplitHi : split ≤ hi) :
    roughSmoothPhysicalBlock lo split hi y alpha broad =
      alpha *
          ((FriableAsymptotic.friableCount hi y : ℝ) -
            (FriableAsymptotic.friableCount split y : ℝ)) +
        broad *
          ((FriableAsymptotic.friableCount split y : ℝ) -
            (FriableAsymptotic.friableCount lo y : ℝ)) := by
  have hPsiLoSplit : psi lo y ≤ psi split y :=
    FriableAsymptotic.friableCount_mono_left hloSplit
  have hPsiSplitHi : psi split y ≤ psi hi y :=
    FriableAsymptotic.friableCount_mono_left hSplitHi
  rw [roughSmoothPhysicalBlock,
    smoothInterval_card_eq_psi_sub hSplitHi,
    smoothInterval_card_eq_psi_sub hloSplit,
    Nat.cast_sub hPsiSplitHi, Nat.cast_sub hPsiLoSplit]
  rfl



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

/- Source module: Erdos390.WholePaper.RoughBalancedFriableResidualReduction -/
section


/-!
# Residual cancellation in the balanced four-endpoint friable block

The closed de Bruijn theorem controls the endpoint residual

`R(X,y) = Psi(X,y) - X * rho(log X / log y)`

by `O(X / log y)`.  Applying that estimate independently at four
endpoints loses one logarithm.  This file avoids that lossy triangle
inequality.  It proves that the literal four-endpoint residual is exactly
two *short residual increments* plus one broad increment whose coefficient
already contains `1/L`.

It also records the exact reverse Buchstab recurrence for `R`, using one
common prime interval for both endpoints.  The remaining missing analytic
input is thereby reduced to a local regularity inequality for `R`; it is
strictly an estimate for the genuine friable counting function and contains
no selector, row, rounding, or feasibility conclusion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The genuine endpoint residual -/















/-! ## Exact reverse Buchstab recurrence for the residual -/













/-! ## Verified regularity of the Dickman main term -/

/-- Symmetric compact one-Lipschitz control of the already constructed
Dickman function. -/
theorem roughRho_abs_sub_le_abs_of_le_five
    {a b : ℝ} (ha5 : a ≤ 5) (hb5 : b ≤ 5) :
    |rho a - rho b| ≤ |a - b| := by
  by_cases hab : a ≤ b
  · have h := FriableAsymptotic.rho_lipschitz_of_le_five hab hb5
    rw [abs_sub_comm (rho a), abs_sub_comm a]
    exact h.trans_eq (abs_of_nonneg (sub_nonneg.mpr hab)).symm
  · have hba : b ≤ a := le_of_not_ge hab
    have h := FriableAsymptotic.rho_lipschitz_of_le_five hba ha5
    exact h.trans_eq (abs_of_nonneg (sub_nonneg.mpr hba)).symm





/-! ## The literal four-endpoint residual collapse -/









/-- Exact main-plus-transition decomposition of the literal four endpoint
count.  In particular, no triangle inequality has yet been applied to the
four de Bruijn residuals. -/
theorem roughPhysicalFriableCombination_eq_main_add_residualTransition
    (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) :
    roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y =
      roughPhysicalDickmanCombination δ α β L
          Xplus X Xminus Xhalf y +
        roughPhysicalResidualTransition δ α β L
          Xplus X Xminus Xhalf y := by
  simp only [roughPhysicalFriableCombination,
    roughPhysicalDickmanCombination, Fin.sum_univ_four]
  simp [roughPhysicalBlockCoefficient, roughPhysicalNatEndpoint]
  unfold roughPhysicalResidualTransition roughFriableResidual
  ring

/-! ## The one remaining analytic inequality -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasNormalization -/
section


/-!
# The finite de Bruijn--Saias normal form on the five Dickman faces

Section 8.5 of the paper uses the integration-by-parts identity

`Lambda(z,y) = z * G_y(log z / log y) - fract z`,

where

`G_y(u) = rho(u) - integral rho'(u-v) * fract(y^v) * y^(-v) dv`.

This file formalizes the finite normal form, its exact initial face, the
compact bounded-variation datum behind the asserted Lipschitz estimate, and
the exact way in which this normalization enters the already isolated rough
prime-transition ledger.

The cited Hildebrand--Tenenbaum--Saias estimate for `Psi - Lambda` is not
proved in the paper.  Accordingly, no theorem below declares that estimate
as an axiom.  Its precise endpoint-shaped consequence is exposed as a `Prop`
which can be passed to a reduction theorem.  In particular, the endpoint
error remains proportional to `A+B`, not to the short gap `B-A`.
-/

open scoped BigOperators Interval ENNReal

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The finite `G_y` normal form -/













theorem roughSaiasDickmanDerivative_of_one_le
    {u : ℝ} (hu : 1 ≤ u) :
    roughSaiasDickmanDerivative u = -rho (u - 1) / u := by
  simp [roughSaiasDickmanDerivative, not_lt.mpr hu]



theorem measurable_roughSaiasDickmanDerivative :
    Measurable roughSaiasDickmanDerivative := by
  unfold roughSaiasDickmanDerivative
  apply Measurable.ite measurableSet_Iio measurable_const
  exact (continuous_rho.measurable.comp
    (measurable_id.sub_const 1)).neg.div measurable_id

theorem continuous_roughSaiasBaseRpow {y : ℕ} (hy : 0 < y) :
    Continuous (fun v : ℝ => (y : ℝ) ^ v) := by
  exact Real.continuous_const_rpow (by positivity)

theorem measurable_roughSaiasFractionalWeight {y : ℕ} (hy : 0 < y) :
    Measurable (roughSaiasFractionalWeight y) := by
  have hpow : Continuous (fun v : ℝ => (y : ℝ) ^ v) :=
    continuous_roughSaiasBaseRpow hy
  have hpowNeg : Continuous (fun v : ℝ => (y : ℝ) ^ (-v)) :=
    hpow.comp continuous_neg
  exact hpow.measurable.fract.mul hpowNeg.measurable

/-- The fractional Saias weight is uniformly between zero and one on the
integration interval. -/
theorem roughSaiasFractionalWeight_mem_unitInterval
    {y : ℕ} (hy : 1 ≤ y) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ roughSaiasFractionalWeight y v ∧
      roughSaiasFractionalWeight y v ≤ 1 := by
  have hbase : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hpowNonneg : 0 ≤ (y : ℝ) ^ (-v) :=
    Real.rpow_nonneg (by positivity) _
  have hpowLe : (y : ℝ) ^ (-v) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have hfractNonneg : 0 ≤ Int.fract ((y : ℝ) ^ v) :=
    Int.fract_nonneg _
  have hfractLe : Int.fract ((y : ℝ) ^ v) ≤ 1 :=
    (Int.fract_lt_one _).le
  unfold roughSaiasFractionalWeight
  constructor
  · exact mul_nonneg hfractNonneg hpowNonneg
  · calc
      Int.fract ((y : ℝ) ^ v) * (y : ℝ) ^ (-v) ≤
          1 * (y : ℝ) ^ (-v) :=
        mul_le_mul_of_nonneg_right hfractLe hpowNonneg
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hpowLe (by norm_num)
      _ = 1 := mul_one _

/-- The right-limit Dickman derivative has absolute value at most one on
the whole compact interval that can occur in the convolution. -/
theorem roughSaiasDickmanDerivative_abs_le_one
    {u : ℝ} (hu5 : u ≤ 5) :
    |roughSaiasDickmanDerivative u| ≤ 1 := by
  by_cases hu1 : u < 1
  · simp [roughSaiasDickmanDerivative, hu1]
  · have hu1' : 1 ≤ u := le_of_not_gt hu1
    have hb := FriableAsymptotic.rho_delay_integrand_bounds hu1' hu5
    rw [roughSaiasDickmanDerivative_of_one_le hu1', neg_div, abs_neg,
      abs_of_nonneg hb.1]
    exact hb.2

/-- The unweighted translated derivative is interval-integrable on the
fixed compact interval. -/
theorem roughSaiasDickmanDerivative_translate_intervalIntegrable
    {u : ℝ} (hu5 : u ≤ 5) :
    IntervalIntegrable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v))
      volume 0 5 := by
  have hmeas : Measurable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v)) :=
    measurable_roughSaiasDickmanDerivative.comp
      (measurable_const.sub measurable_id)
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 5 :=
    continuous_const.intervalIntegrable 0 5
  apply hone.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  have hv' : v ∈ Icc (0 : ℝ) 5 := by
    have hvIoc : v ∈ Ioc (0 : ℝ) 5 := by
      simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using hv
    exact ⟨hvIoc.1.le, hvIoc.2⟩
  simpa only [Real.norm_eq_abs, norm_one] using
    roughSaiasDickmanDerivative_abs_le_one
      (u := u - v) (by linarith [hv'.1])

/-- The complete integrand in the finite Saias normal form is
interval-integrable. -/
theorem roughSaiasIntegrand_intervalIntegrable
    {y : ℕ} (hy2 : 2 ≤ y) {u : ℝ} (hu5 : u ≤ 5) :
    IntervalIntegrable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v) *
        roughSaiasFractionalWeight y v)
      volume 0 5 := by
  have hmeas : Measurable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v) *
        roughSaiasFractionalWeight y v) :=
    (measurable_roughSaiasDickmanDerivative.comp
      (measurable_const.sub measurable_id)).mul
        (measurable_roughSaiasFractionalWeight (by omega))
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 5 :=
    continuous_const.intervalIntegrable 0 5
  apply hone.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  have hv' : v ∈ Icc (0 : ℝ) 5 := by
    have hvIoc : v ∈ Ioc (0 : ℝ) 5 := by
      simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using hv
    exact ⟨hvIoc.1.le, hvIoc.2⟩
  have hderiv := roughSaiasDickmanDerivative_abs_le_one
    (u := u - v) (by linarith [hv'.1])
  have hweight := roughSaiasFractionalWeight_mem_unitInterval
    (y := y) (by omega) hv'.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight.1]
  calc
    |roughSaiasDickmanDerivative (u - v)| *
        roughSaiasFractionalWeight y v ≤
      1 * roughSaiasFractionalWeight y v :=
        mul_le_mul_of_nonneg_right hderiv hweight.1
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hweight.2 (by norm_num)
    _ = 1 := mul_one _











/-! ## The bounded-variation datum and compact Lipschitz reduction -/

/-- The finite Dickman function is antitone on the whole nonnegative compact
range.  The existing library theorem starts at `1`; the initial interval is
filled in here using the exact constant branch. -/
theorem roughRho_antitoneOn_zero_five :
    AntitoneOn rho (Icc (0 : ℝ) 5) := by
  intro a ha b hb hab
  by_cases hb1 : b ≤ 1
  · rw [rho_eq_one_of_le_one hb1,
      rho_eq_one_of_le_one (hab.trans hb1)]
  by_cases ha1 : 1 ≤ a
  · exact antitoneOn_rho_one_five
      ⟨ha1, ha.2⟩ ⟨(le_of_not_ge hb1), hb.2⟩ hab
  · rw [rho_eq_one_of_le_one (le_of_not_ge ha1)]
    exact FriableAsymptotic.rho_le_one_of_le_five hb.2

/-- On the left of its single jump, the right-limit derivative extension is
antitone. -/
theorem roughSaiasDickmanDerivative_antitoneOn_left :
    AntitoneOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) := by
  intro a ha b hb hab
  by_cases hb1 : b < 1
  · have ha1 : a < 1 := hab.trans_lt hb1
    simp [roughSaiasDickmanDerivative_of_lt_one ha1,
      roughSaiasDickmanDerivative_of_lt_one hb1]
  · have hbEq : b = 1 := le_antisymm hb.2 (le_of_not_gt hb1)
    subst b
    by_cases ha1 : a < 1
    · rw [roughSaiasDickmanDerivative_of_lt_one ha1,
        roughSaiasDickmanDerivative_one]
      norm_num
    · have haEq : a = 1 :=
        le_antisymm hab (le_of_not_gt ha1)
      subst a
      exact le_rfl

/-- To the right of the jump, the Dickman derivative increases from `-1`
towards zero. -/
theorem roughSaiasDickmanDerivative_monotoneOn_right :
    MonotoneOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) := by
  intro a ha b hb hab
  have hrho : rho (b - 1) ≤ rho (a - 1) := by
    apply roughRho_antitoneOn_zero_five
    · constructor <;> linarith [ha.1, ha.2]
    · constructor <;> linarith [hb.1, hb.2]
    · linarith
  have hrhoA : 0 ≤ rho (a - 1) :=
    (rho_pos_on_zero_five (by linarith [ha.1])
      (by linarith [ha.2])).le
  have hfirst : rho (b - 1) / b ≤ rho (a - 1) / b :=
    div_le_div_of_nonneg_right hrho (by linarith [hb.1])
  have hsecond : rho (a - 1) / b ≤ rho (a - 1) / a :=
    div_le_div_of_nonneg_left hrhoA (by linarith [ha.1]) hab
  have hratio : rho (b - 1) / b ≤ rho (a - 1) / a :=
    hfirst.trans hsecond
  rw [roughSaiasDickmanDerivative_of_one_le ha.1,
    roughSaiasDickmanDerivative_of_one_le hb.1]
  calc
    -rho (a - 1) / a = -(rho (a - 1) / a) := by ring
    _ ≤ -(rho (b - 1) / b) := neg_le_neg hratio
    _ = -rho (b - 1) / b := by ring

/-- Negation does not change total variation of a real-valued function. -/
theorem eVariationOn_neg_real (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => -f x) s = eVariationOn f s := by
  simp only [eVariationOn, edist_neg_neg]

/-- The exact compact variation datum used by the proof in the paper.  The
single jump contributes one and the monotone right branch contributes at
most one, so the total variation is at most two. -/
theorem roughSaiasDickmanDerivative_eVariationOn_le_two :
    eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 5) ≤
      ENNReal.ofReal 2 := by
  have hleftMono : MonotoneOn
      (fun u : ℝ => -roughSaiasDickmanDerivative u)
      (Icc (-5 : ℝ) 1) := by
    intro a ha b hb hab
    exact neg_le_neg
      (roughSaiasDickmanDerivative_antitoneOn_left ha hb hab)
  have hleftNeg :
      eVariationOn (fun u : ℝ => -roughSaiasDickmanDerivative u)
          (Icc (-5 : ℝ) 1) ≤ ENNReal.ofReal 1 := by
    have hraw := hleftMono.eVariationOn_le
      (a := (-5 : ℝ)) (b := (1 : ℝ))
      (by norm_num) (by norm_num)
    norm_num [roughSaiasDickmanDerivative] at hraw
    simpa only [roughSaiasDickmanDerivative, ENNReal.ofReal_one] using hraw
  have hleft :
      eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) ≤
        ENNReal.ofReal 1 := by
    rw [← eVariationOn_neg_real roughSaiasDickmanDerivative
      (Icc (-5 : ℝ) 1)]
    exact hleftNeg
  have hrightRaw :=
    roughSaiasDickmanDerivative_monotoneOn_right.eVariationOn_le
      (a := (1 : ℝ)) (b := (5 : ℝ))
      (by norm_num) (by norm_num)
  have hrightRaw' :
      eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) ≤
        ENNReal.ofReal
          (roughSaiasDickmanDerivative 5 -
            roughSaiasDickmanDerivative 1) := by
    simpa using hrightRaw
  have hq5 : roughSaiasDickmanDerivative 5 ≤ 0 := by
    rw [roughSaiasDickmanDerivative_of_one_le (by norm_num)]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr
        (rho_pos_on_zero_five (by norm_num) (by norm_num)).le)
      (by norm_num)
  have hright :
      eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) ≤
        ENNReal.ofReal 1 := by
    apply hrightRaw'.trans
    apply ENNReal.ofReal_le_ofReal
    rw [roughSaiasDickmanDerivative_one]
    linarith
  have hadd :
      eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) +
        eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) =
      eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 5) := by
    simpa only [univ_inter] using
      (eVariationOn.Icc_add_Icc
        (f := roughSaiasDickmanDerivative) (s := (Set.univ : Set ℝ))
        (a := (-5 : ℝ)) (b := (1 : ℝ)) (c := (5 : ℝ))
        (by norm_num) (by norm_num) (by simp))
  calc
    eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 5) =
        eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) +
          eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) :=
      hadd.symm
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal 1 := add_le_add hleft hright
    _ = ENNReal.ofReal 2 := by norm_num





/-- Application of the standard compact BV translation principle to the
actual Dickman derivative, using the proved variation constant `2`. -/
theorem roughSaiasDickmanDerivative_translation_le_two
    (hBV : RoughCompactBVTranslationPrinciple)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    (∫ v in (0 : ℝ)..5,
      |roughSaiasDickmanDerivative (a - v) -
        roughSaiasDickmanDerivative (b - v)|) ≤
      2 * |a - b| := by
  exact hBV roughSaiasDickmanDerivative
    roughSaiasDickmanDerivative_eVariationOn_le_two ha hb





/-! ## The explicit `1 / log y` normalization correction -/











/-! ## Exact connection to the genuine friable residual -/











/-- Exact decomposition of the already-defined genuine residual. -/
theorem roughFriableResidual_eq_saiasError_add_correction (X y : ℕ) :
    roughFriableResidual X y =
      roughSaiasEndpointError X y + roughSaiasDickmanCorrection X y := by
  unfold roughFriableResidual roughFriableDickmanMain
    roughSaiasEndpointError roughSaiasNaturalMain
    roughSaiasDickmanCorrection
  ring



/-- Exact finite-difference decomposition of the genuine friable residual. -/
theorem roughFriableResidual_difference_eq_saias
    (A B y : ℕ) :
    roughFriableResidual B y - roughFriableResidual A y =
      (roughSaiasEndpointError B y - roughSaiasEndpointError A y) +
        (roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y) := by
  rw [roughFriableResidual_eq_saiasError_add_correction,
    roughFriableResidual_eq_saiasError_add_correction]
  ring







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasWeightedTransition -/
section


/-!
# Paper-scale weighted Saias transitions

The local residual predicate used by the method-of-steps development asks
for a short-interval estimate at every pair of natural endpoints.  That is
stronger than the Hildebrand--Tenenbaum--Saias input used in the paper.
The paper only needs one fixed four-endpoint block.  In that block the two
short increments have coefficients `1` and `delta * alpha`, while the broad
half-scale increment already has the coefficient `delta * beta / L`.

This file records that weaker and directly usable interface.  The endpoint
HT--Saias envelope contributes

`eta(y) * (A + B) + 5 * (B - A) / log y`

to a specified pair.  We retain those three contributions with their exact
block coefficients and close them to the existing
`roughPhysicalFriableCombination`.  No universal adjacent-pair regularity,
prime-transition predicate, selector conclusion, or new axiom is assumed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-! ## A transition budget for one specified pair -/



/-- HT--Saias endpoint approximation gives the desired residual increment
bound at any *specified* ordered pair.  Unlike the prime-transition ledger
form, this statement also covers the initial face `B <= y`; no reverse
Buchstab recurrence or universal local predicate is needed. -/
theorem roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ A B y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hA : 0 < A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableResidual B y - roughFriableResidual A y| ≤
      roughSaiasPairTransitionBudget eta A B y := by
  have hB : 0 < B := hA.trans_le hAB
  have hlogA : Real.log (A : ℝ) ≤
      5 * Real.log (y : ℝ) := by
    have hABlog : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
      Real.log_le_log (by exact_mod_cast hA) (by exact_mod_cast hAB)
    exact hABlog.trans hlogB
  have herrorA : |roughSaiasEndpointError A y| ≤ eta y * (A : ℝ) :=
    happrox hY hy2 hA hlogA
  have herrorB : |roughSaiasEndpointError B y| ≤ eta y * (B : ℝ) :=
    happrox hY hy2 hB hlogB
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hB5 : FriableAsymptotic.dickmanU B y ≤ 5 := by
    dsimp [FriableAsymptotic.dickmanU]
    exact (div_le_iff₀ hlogy).2 hlogB
  have hcorrection := roughSaiasDickmanCorrection_difference_abs_le
    hBV hA hAB hy2 hB5
  rw [roughFriableResidual_difference_eq_saias]
  calc
    |(roughSaiasEndpointError B y - roughSaiasEndpointError A y) +
        (roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y)| ≤
      |roughSaiasEndpointError B y - roughSaiasEndpointError A y| +
        |roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y| := abs_add_le _ _
    _ ≤ (|roughSaiasEndpointError B y| +
          |roughSaiasEndpointError A y|) +
        |roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y| := by
      exact add_le_add (abs_sub _ _) le_rfl
    _ ≤ (eta y * (B : ℝ) + eta y * (A : ℝ)) +
        5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) :=
      add_le_add (add_le_add herrorB herrorA) hcorrection
    _ = roughSaiasPairTransitionBudget eta A B y := by
      unfold roughSaiasPairTransitionBudget
      ring

/-! ## The literal weighted four-endpoint block -/





/-- The complete residual part of the physical block is bounded by the
three *weighted* Saias pair ledgers.  In particular, no
`RoughFriableResidualLocalRegularity` or
`RoughFriablePrimeTransitionEstimateUpToFive` premise appears. -/
theorem roughPhysicalResidualTransition_abs_le_of_saiasEndpointApproximation
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ : ℕ}
    {δ α β L : ℝ} {Xplus X Xminus Xhalf y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    |roughPhysicalResidualTransition δ α β L
        Xplus X Xminus Xhalf y| ≤
      roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y := by
  have hminus : 0 < Xminus := hhalf.trans_le hHalfMinus
  have hx : 0 < X := hminus.trans_le hMinusX
  have hupper :=
    roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
      hBV happrox hY hy2 hx hXPlus (hlogs (0 : Fin 4))
  have hlower :=
    roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
      hBV happrox hY hy2 hminus hMinusX (hlogs (1 : Fin 4))
  have hbroad :
      |roughFriableResidual Xhalf y - roughFriableResidual Xminus y| ≤
        roughSaiasPairTransitionBudget eta Xhalf Xminus y := by
    simpa only [abs_sub_comm] using
      roughFriableResidual_difference_abs_le_of_saiasEndpointApproximation
        hBV happrox hY hy2 hhalf hHalfMinus (hlogs (2 : Fin 4))
  unfold roughPhysicalResidualTransition
  calc
    |(roughFriableResidual Xplus y - roughFriableResidual X y) -
        δ * α *
          (roughFriableResidual X y - roughFriableResidual Xminus y) +
        δ * (β / L) *
          (roughFriableResidual Xhalf y -
            roughFriableResidual Xminus y)| ≤
      |roughFriableResidual Xplus y - roughFriableResidual X y| +
        |δ * α| *
          |roughFriableResidual X y - roughFriableResidual Xminus y| +
        |δ * (β / L)| *
          |roughFriableResidual Xhalf y -
            roughFriableResidual Xminus y| := by
      calc
        _ ≤ |(roughFriableResidual Xplus y -
                roughFriableResidual X y) -
              δ * α *
                (roughFriableResidual X y -
                  roughFriableResidual Xminus y)| +
            |δ * (β / L) *
              (roughFriableResidual Xhalf y -
                roughFriableResidual Xminus y)| := abs_add_le _ _
        _ ≤ (|roughFriableResidual Xplus y -
                roughFriableResidual X y| +
              |δ * α *
                (roughFriableResidual X y -
                  roughFriableResidual Xminus y)|) +
            |δ * (β / L) *
              (roughFriableResidual Xhalf y -
                roughFriableResidual Xminus y)| := by
          exact add_le_add (abs_sub _ _) le_rfl
        _ = _ := by simp only [abs_mul]
    _ ≤ roughSaiasPairTransitionBudget eta X Xplus y +
        |δ * α| * roughSaiasPairTransitionBudget eta Xminus X y +
        |δ * (β / L)| *
          roughSaiasPairTransitionBudget eta Xhalf Xminus y := by
      exact add_le_add
        (add_le_add hupper
          (mul_le_mul_of_nonneg_left hlower (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hbroad (abs_nonneg _))
    _ = roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y := rfl

/-- The paper-scale weighted transition closes directly to the existing
four-endpoint friable selector expression.  The first summand is entirely
deterministic.  The second is the three-pair HT--Saias ledger above. -/
theorem roughPhysicalFriableCombination_abs_le_of_saiasEndpointApproximation
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ : ℕ}
    {δ α β L : ℝ} {Xplus X Xminus Xhalf y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    |roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y| ≤
      roughPhysicalDickmanTransitionLedger δ α β L
          Xplus X Xminus Xhalf y +
        roughPhysicalSaiasTransitionBudget eta δ α β L
          Xplus X Xminus Xhalf y := by
  have hminus : 0 < Xminus := hhalf.trans_le hHalfMinus
  have hx : 0 < X := hminus.trans_le hMinusX
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hcoordinate5 : ∀ i : Fin 4,
      FriableAsymptotic.dickmanU
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y ≤ 5 := by
    intro i
    simp only [FriableAsymptotic.dickmanU]
    exact (div_le_iff₀ hlogY).2 (hlogs i)
  have hbase5 : FriableAsymptotic.dickmanU X y ≤ 5 := by
    have h := hcoordinate5 (1 : Fin 4)
    simpa only [roughPhysicalNatEndpoint] using h
  have hbase0 : 0 ≤ FriableAsymptotic.dickmanU X y := by
    simp only [FriableAsymptotic.dickmanU]
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega)))
      hlogY.le
  have hmain :
      |roughPhysicalDickmanCombination δ α β L
          Xplus X Xminus Xhalf y| ≤
        roughPhysicalDickmanTransitionLedger δ α β L
          Xplus X Xminus Xhalf y := by
    simpa only [roughPhysicalDickmanCombination,
      roughPhysicalDickmanTransitionLedger] using
      roughFriableMain_abs_le_with_balanceError
        (I := Finset.univ)
        (coeff := roughPhysicalBlockCoefficient δ α β L)
        (endpoint := roughPhysicalNatEndpoint
          Xplus X Xminus Xhalf)
        (base := X) (y := y)
        (fun i _hi ↦ hcoordinate5 i) hbase0 hbase5
  have htransition :
      |roughPhysicalResidualTransition δ α β L
          Xplus X Xminus Xhalf y| ≤
        roughPhysicalSaiasTransitionBudget eta δ α β L
          Xplus X Xminus Xhalf y :=
    roughPhysicalResidualTransition_abs_le_of_saiasEndpointApproximation
      (δ := δ) (α := α) (β := β) (L := L)
      hBV happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs
  rw [roughPhysicalFriableCombination_eq_main_add_residualTransition]
  calc
    |roughPhysicalDickmanCombination δ α β L
          Xplus X Xminus Xhalf y +
        roughPhysicalResidualTransition δ α β L
          Xplus X Xminus Xhalf y| ≤
      |roughPhysicalDickmanCombination δ α β L
          Xplus X Xminus Xhalf y| +
        |roughPhysicalResidualTransition δ α β L
          Xplus X Xminus Xhalf y| := abs_add_le _ _
    _ ≤ roughPhysicalDickmanTransitionLedger δ α β L
          Xplus X Xminus Xhalf y +
        roughPhysicalSaiasTransitionBudget eta δ α β L
          Xplus X Xminus Xhalf y := add_le_add hmain htransition

/-! ## Paper-scale absorption and selector-facing closure -/

/-- Once the deterministic displacement/rounding ledger and the weighted
HT--Saias ledger have been absorbed at their paper scales, the existing
four-endpoint selector target inherits their sum.  This wrapper does not
weaken that target: its left side is literally
`roughPhysicalFriableCombination`. -/
theorem roughPhysicalFriableCombination_abs_le_of_saiasPaperScale
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ : ℕ}
    {δ α β L mainAllowance transitionAllowance : ℝ}
    {Xplus X Xminus Xhalf y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger δ α β L
        Xplus X Xminus Xhalf y ≤ mainAllowance)
    (htransition : roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y ≤ transitionAllowance) :
    |roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y| ≤
      mainAllowance + transitionAllowance := by
  exact
    (roughPhysicalFriableCombination_abs_le_of_saiasEndpointApproximation
      hBV happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs).trans
      (add_le_add hmain htransition)



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

/-- Coordinate form of the exact high-prime factorization. -/
theorem completeRoughLabel_factorization_apply (y a p : ℕ) :
    (completeRoughLabel y a).factorization p =
      if y < p then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeRoughLabel_factorization_eq_filter_gt y a)
  simpa only [Finsupp.filter_apply] using h

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

/-- Nonzero high-part coordinates lie strictly above the cutoff. -/
theorem completeRoughLabel_factorization_support
    {y a p : ℕ}
    (hp : (completeRoughLabel y a).factorization p ≠ 0) :
    y < p := by
  rw [completeRoughLabel_factorization_apply] at hp
  by_contra hpHigh
  simp [hpHigh] at hp

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

/- Source module: Erdos390.WholePaper.FloatingRoundingRows -/
section


/-!
# Integer row sums force two fractional coordinates

After integral coordinates are frozen, an active row cannot contain exactly
one fractional coordinate: the whole row sum is an integer and every other
entry is zero or one.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



@[simp]
theorem mem_rowSet {A R : Type*} [Fintype A]
    {row : A → R} {r : R} {a : A} :
    a ∈ rowSet row r ↔ row a = r := by
  classical
  simp [rowSet]





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CanonicalCompleteRoughRows -/
section


/-!
# Canonical complete rough rows for exactification

A finite candidate set itself supplies the coordinate type used by floating
rounding.  Its attained complete rough labels supply a canonical finite row
type.  The row signature is simply factorization of the label; positivity
of attained labels and uniqueness of factorization make this signature map
injective.

This file also identifies `rowSet` with the literal complete-rough fiber and
provides the value, interval, summation, and row-integrality bridges required
by the exactification interface.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Canonical finite types and maps -/



















/-! ## Signature and value interfaces -/

/-- An attained complete rough label is positive. -/
theorem canonicalCompleteRoughRow_label_pos
    (y : ℕ) (A : Finset ℕ)
    (row : CanonicalCompleteRoughRow y A) :
    0 < row.1 := by
  obtain ⟨a, _ha, hlabel⟩ :=
    mem_completeRoughLabelSet.mp row.property
  rw [← hlabel, completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp





/-- The underlying-value map on the candidate subtype is injective. -/
theorem canonicalCompleteRoughCandidateValue_injective
    (A : Finset ℕ) :
    Function.Injective (canonicalCompleteRoughCandidateValue A) := by
  intro a b hab
  apply Subtype.ext
  exact hab



/-! ## Literal subtype fibers and `rowSet` -/







/-- Membership in the floating-rounding `rowSet` is exactly ambient row
fiber membership of the candidate value. -/
theorem mem_canonicalCompleteRoughRowSet_iff
    {y : ℕ} {A : Finset ℕ}
    {row : CanonicalCompleteRoughRow y A}
    {a : CompleteRoughCandidate A} :
    a ∈ rowSet (canonicalCompleteRoughRow y A) row ↔
      canonicalCompleteRoughCandidateValue A a ∈
        completeRoughRowFiber y A row.1 := by
  rw [mem_rowSet, mem_completeRoughRowFiber]
  constructor
  · intro hrow
    refine ⟨a.property, ?_⟩
    have hval := congrArg Subtype.val hrow
    simpa only [canonicalCompleteRoughRow,
      canonicalCompleteRoughCandidateValue] using hval
  · rintro ⟨_ha, hlabel⟩
    apply Subtype.ext
    simpa only [canonicalCompleteRoughRow,
      canonicalCompleteRoughCandidateValue] using hlabel



/-! ## Summation and integrality bridges -/

/-- Reindexing a canonical `rowSet` by underlying candidate values gives
the sum over the literal ambient complete rough fiber. -/
theorem sum_canonicalCompleteRoughRowSet_eq_sum_completeRoughRowFiber
    {W : Type*} [AddCommMonoid W]
    (y : ℕ) (A : Finset ℕ) (weight : ℕ → W)
    (row : CanonicalCompleteRoughRow y A) :
    ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
        weight (canonicalCompleteRoughCandidateValue A a) =
      ∑ value ∈ completeRoughRowFiber y A row.1,
        weight value := by
  classical
  apply Finset.sum_bij
    (fun a _ha ↦ canonicalCompleteRoughCandidateValue A a)
  · intro a ha
    exact mem_canonicalCompleteRoughRowSet_iff.mp ha
  · intro a₁ _ha₁ a₂ _ha₂ hvalue
    exact canonicalCompleteRoughCandidateValue_injective A hvalue
  · intro value hvalue
    let a : CompleteRoughCandidate A :=
      ⟨value, (mem_completeRoughRowFiber.mp hvalue).1⟩
    refine ⟨a, ?_, ?_⟩
    · apply mem_canonicalCompleteRoughRowSet_iff.mpr
      simpa only [a, canonicalCompleteRoughCandidateValue] using hvalue
    · simp only [a, canonicalCompleteRoughCandidateValue]
  · intro a _ha
    rfl









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







/-- Every attained canonical row label has the intrinsic complete-rough
support property. -/
theorem isCompleteRoughLabel_of_canonicalCompleteRoughRow
    {y : ℕ} {A : Finset ℕ}
    (row : CanonicalCompleteRoughRow y A) :
    IsCompleteRoughLabel y row.1 := by
  constructor
  · exact canonicalCompleteRoughRow_label_pos y A row
  · obtain ⟨a, _ha, hlabel⟩ := mem_completeRoughLabelSet.mp row.2
    intro p hp
    rw [← hlabel] at hp
    exact completeRoughLabel_factorization_support hp

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

/-- A complete-rough label is coprime to the fixed head modulus whenever
the head cutoff is at most the smooth cutoff. -/
theorem isCompleteRoughLabel_coprime_roughHeadModulus
    {W y label : ℕ} (hWy : W ≤ y)
    (hlabel : IsCompleteRoughLabel y label) :
    Nat.Coprime label (roughHeadModulus W) := by
  by_contra hnot
  obtain ⟨p, hpPrime, hpLabel, hpHead⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpFactor := hpPrime.factorization_pos_of_dvd hlabel.1.ne' hpLabel
  have hpHigh : y < p := hlabel.2 p hpFactor.ne'
  have hheadSmooth : roughHeadModulus W ∈
      Nat.smoothNumbers (y + 1) :=
    roughHeadModulus_mem_smoothNumbers hWy
  have hpLow :=
    (Nat.mem_smoothNumbers').mp hheadSmooth p hpPrime hpHead
  omega

/-- Head-free version of the exact row-to-smooth-quotient reindexing. -/
theorem completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
    {W lo hi y label : ℕ}
    (hlabel : IsCompleteRoughLabel y label)
    (hcop : Nat.Coprime label (roughHeadModulus W)) :
    (completeRoughRowFiber y
        (roughHeadFree W (Finset.Ioc lo hi)) label).card =
      (roughHeadFreeSmoothInterval W (lo / label) (hi / label) y).card := by
  apply Finset.card_bij (fun a _ha ↦ a / label)
  · intro a ha
    rw [mem_completeRoughRowFiber] at ha
    have haHead := mem_roughHeadFree.mp ha.1
    have haInterval := Finset.mem_Ioc.mp haHead.1
    have hdvd : label ∣ a := by
      rw [← ha.2]
      exact completeRoughLabel_dvd y a
    apply mem_roughHeadFree.mpr
    constructor
    · apply Erdos390.Full.StructuredCells.mem_smoothInterval.mpr
      constructor
      · apply (Nat.div_lt_iff_lt_mul hlabel.1).mpr
        simpa [Nat.div_mul_cancel hdvd] using haInterval.1
      · constructor
        · apply (Nat.le_div_iff_mul_le hlabel.1).mpr
          simpa [Nat.div_mul_cancel hdvd] using haInterval.2
        · have haPos : 0 < a := Nat.zero_lt_of_lt haInterval.1
          simpa only [completeSmoothPart, ha.2] using
            completeSmoothPart_mem_smoothNumbers (y := y) haPos
    · rw [← Nat.div_mul_cancel hdvd] at haHead
      exact (Nat.coprime_mul_iff_left.mp haHead.2).1
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
    have hsHead := mem_roughHeadFree.mp hs
    have hsData :=
      Erdos390.Full.StructuredCells.mem_smoothInterval.mp hsHead.1
    refine ⟨label * s, ?_, ?_⟩
    · apply mem_completeRoughRowFiber.mpr
      constructor
      · apply mem_roughHeadFree.mpr
        constructor
        · apply Finset.mem_Ioc.mpr
          constructor
          · have hlo := (Nat.div_lt_iff_lt_mul hlabel.1).mp hsData.1
            simpa only [Nat.mul_comm] using hlo
          · have hhi := (Nat.le_div_iff_mul_le hlabel.1).mp hsData.2.1
            simpa only [Nat.mul_comm] using hhi
        · exact Nat.coprime_mul_iff_left.mpr ⟨hcop, hsHead.2⟩
      · exact completeRoughLabel_mul_eq_of_isCompleteRoughLabel_of_smooth
          hlabel hsData.2.2
    · simpa only [Nat.mul_comm] using Nat.mul_div_left s hlabel.1

/-- The literal upper canonical-row quota is exactly the difference of the
two friable counts at the quotient endpoints. -/
theorem roughUpperCompleteRoughRowTarget_eq_friableEndpoints
    {n h K y : ℕ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      (FriableAsymptotic.friableCount ((2 * n + h) / row.1) y : ℝ) -
        (FriableAsymptotic.friableCount ((2 * n) / row.1) y : ℝ) := by
  have hlabel :=
    isCompleteRoughLabel_of_canonicalCompleteRoughRow row
  have hlohi : (2 * n) / row.1 ≤ (2 * n + h) / row.1 :=
    Nat.div_le_div_right (by omega)
  have hmono := FriableAsymptotic.friableCount_mono_left (y := y) hlohi
  have hcard : roughUpperCompleteRoughRowTarget n h y row.1 =
      FriableAsymptotic.friableCount ((2 * n + h) / row.1) y -
        FriableAsymptotic.friableCount ((2 * n) / row.1) y := by
    unfold roughUpperCompleteRoughRowTarget roughUpperBlock
    rw [completeRoughRowFiber_Ioc_card_eq_smoothInterval hlabel,
      Erdos390.Full.StructuredCells.smoothInterval_card_eq_psi_sub hlohi]
    rfl
  rw [hcard, Nat.cast_sub hmono]

/-- Exact decomposition of one literal raw row into its head-free high and
broad row cardinalities. -/
theorem roughHeadCompatibleRawRowMass_eq_headFreeRowCards
    (W n h K y label : ℕ) (α β L : ℝ) :
    roughHeadCompatibleRawRowMass W n h K y label α β L =
      α * ((completeRoughRowFiber y
        (roughHeadFree W (roughHighLowerBlock n h K)) label).card : ℝ) +
      (β / L) * ((completeRoughRowFiber y
        (roughHeadFree W (roughBroadLowerBlock n h K)) label).card : ℝ) := by
  let labelPred : ℕ → Prop := fun a ↦ completeRoughLabel y a = label
  have hblocks :=
    roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K
  have hfiltered : Disjoint
      ((roughHighLowerBlock n h K).filter labelPred)
      ((roughBroadLowerBlock n h K).filter labelPred) :=
    hblocks.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hhigh :
      (∑ a ∈ (roughHighLowerBlock n h K).filter labelPred,
        roughHeadCompatibleRawWeight W n h K α β L a) =
      α * ((completeRoughRowFiber y
        (roughHeadFree W (roughHighLowerBlock n h K)) label).card : ℝ) := by
    calc
      (∑ a ∈ (roughHighLowerBlock n h K).filter labelPred,
          roughHeadCompatibleRawWeight W n h K α β L a) =
        ∑ a ∈ (roughHighLowerBlock n h K).filter labelPred,
          if Nat.Coprime a (roughHeadModulus W) then α else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have haHigh := (Finset.mem_filter.mp ha).1
        have haBroad : a ∉ roughBroadLowerBlock n h K := by
          intro haBroad
          exact Finset.disjoint_left.mp hblocks haHigh haBroad
        by_cases hcop : Nat.Coprime a (roughHeadModulus W) <;>
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            haHigh, haBroad, hcop]
      _ = α * ((completeRoughRowFiber y
          (roughHeadFree W (roughHighLowerBlock n h K)) label).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp [completeRoughRowFiber, roughHeadFree, labelPred,
          Finset.filter_filter, and_comm]
        ring
  have hbroad :
      (∑ a ∈ (roughBroadLowerBlock n h K).filter labelPred,
        roughHeadCompatibleRawWeight W n h K α β L a) =
      (β / L) * ((completeRoughRowFiber y
        (roughHeadFree W (roughBroadLowerBlock n h K)) label).card : ℝ) := by
    calc
      (∑ a ∈ (roughBroadLowerBlock n h K).filter labelPred,
          roughHeadCompatibleRawWeight W n h K α β L a) =
        ∑ a ∈ (roughBroadLowerBlock n h K).filter labelPred,
          if Nat.Coprime a (roughHeadModulus W) then β / L else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have haBroad := (Finset.mem_filter.mp ha).1
        have haHigh : a ∉ roughHighLowerBlock n h K := by
          intro haHigh
          exact Finset.disjoint_left.mp hblocks haHigh haBroad
        by_cases hcop : Nat.Coprime a (roughHeadModulus W) <;>
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            haHigh, haBroad, hcop]
      _ = (β / L) * ((completeRoughRowFiber y
          (roughHeadFree W (roughBroadLowerBlock n h K)) label).card : ℝ) := by
        rw [← Finset.sum_filter]
        simp [completeRoughRowFiber, roughHeadFree, labelPred,
          Finset.filter_filter, and_comm]
        ring
  rw [roughHeadCompatibleRawRowMass, completeRoughRowFiber,
    roughRawCandidateSet, Finset.filter_union,
    Finset.sum_union hfiltered, hhigh, hbroad]

/-- The literal raw mass on a canonical row is exactly the head-free smooth
physical block at the four natural quotient endpoints.  No asymptotic or
fixed-head approximation is used here. -/
theorem roughHeadCompatibleRawRowMass_eq_headFreeSmoothPhysicalBlock
    {W n h K y : ℕ} (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (α β L : ℝ) :
    roughHeadCompatibleRawRowMass W n h K y row.1 α β L =
      roughHeadFreeSmoothPhysicalBlock W
        (n / row.1) ((2 * n - K * h) / row.1)
          ((2 * n) / row.1) y α (β / L) := by
  have hlabel :=
    isCompleteRoughLabel_of_canonicalCompleteRoughRow row
  have hcop := isCompleteRoughLabel_coprime_roughHeadModulus hWy hlabel
  rw [roughHeadCompatibleRawRowMass_eq_headFreeRowCards]
  unfold roughHighLowerBlock roughBroadLowerBlock
  rw [completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
      hlabel hcop,
    completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
      hlabel hcop]
  rfl

/-- Exact finite head inclusion--exclusion on one canonical raw row.  This
is the starting point for the separate fixed-head analytic allowance in the
selector-facing theorem. -/
theorem roughHeadCompatibleRawRowMass_eq_headDivisorShift
    {W n h K y : ℕ} (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (α β L : ℝ) :
    roughHeadCompatibleRawRowMass W n h K y row.1 α β L =
      ∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          roughSmoothPhysicalBlock
            ((n / row.1) / d)
            (((2 * n - K * h) / row.1) / d)
            (((2 * n) / row.1) / d) y α (β / L) := by
  rw [roughHeadCompatibleRawRowMass_eq_headFreeSmoothPhysicalBlock
    hWy row α β L,
    roughHeadFreeSmoothPhysicalBlock_eq_divisorShift hWy]

/-- Exact finite-head error ledger.  The literal raw row differs from the
density-scaled unrestricted physical block by at most the sum of the
individual fixed-divisor block shifts.  Thus the canonical consumer needs
only a block-scale fixed-head estimate, never independent endpoint shifts. -/
theorem roughHeadCompatibleRawRowMass_sub_densityPhysicalBlock_abs_le
    {W n h K y : ℕ} (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (α β L : ℝ) :
    |roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
        roughHeadDensity W *
          roughSmoothPhysicalBlock
            (n / row.1) ((2 * n - K * h) / row.1)
              ((2 * n) / row.1) y α (β / L)| ≤
      ∑ d ∈ (roughHeadModulus W).divisors,
        |(ArithmeticFunction.moebius d : ℝ)| *
          |roughSmoothPhysicalBlock
              ((n / row.1) / d)
              (((2 * n - K * h) / row.1) / d)
              (((2 * n) / row.1) / d) y α (β / L) -
            roughSmoothPhysicalBlock
              (n / row.1) ((2 * n - K * h) / row.1)
                ((2 * n) / row.1) y α (β / L) / (d : ℝ)| := by
  let B : ℝ := roughSmoothPhysicalBlock
    (n / row.1) ((2 * n - K * h) / row.1)
      ((2 * n) / row.1) y α (β / L)
  rw [roughHeadCompatibleRawRowMass_eq_headDivisorShift hWy row α β L,
    ← roughHead_moebius_inv_sum_eq_density W, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  change
    |∑ d ∈ (roughHeadModulus W).divisors,
      ((ArithmeticFunction.moebius d : ℝ) *
          roughSmoothPhysicalBlock
            ((n / row.1) / d)
            (((2 * n - K * h) / row.1) / d)
            (((2 * n) / row.1) / d) y α (β / L) -
        ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) * B)| ≤ _
  calc
    _ = |∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          (roughSmoothPhysicalBlock
              ((n / row.1) / d)
              (((2 * n - K * h) / row.1) / d)
              (((2 * n) / row.1) / d) y α (β / L) -
            B / (d : ℝ))| := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _hd
      ring
    _ ≤ ∑ d ∈ (roughHeadModulus W).divisors,
        |(ArithmeticFunction.moebius d : ℝ) *
          (roughSmoothPhysicalBlock
              ((n / row.1) / d)
              (((2 * n - K * h) / row.1) / d)
              (((2 * n) / row.1) / d) y α (β / L) -
            B / (d : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ d ∈ (roughHeadModulus W).divisors,
        |(ArithmeticFunction.moebius d : ℝ)| *
          |roughSmoothPhysicalBlock
              ((n / row.1) / d)
              (((2 * n - K * h) / row.1) / d)
              (((2 * n) / row.1) / d) y α (β / L) -
            roughSmoothPhysicalBlock
              (n / row.1) ((2 * n - K * h) / row.1)
                ((2 * n) / row.1) y α (β / L) / (d : ℝ)| := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [abs_mul]



/-- The exact finite-head ledger bounds precisely the `headAllowance`
expected by the literal selector theorem. -/
theorem roughHeadCompatibleRawRowMass_sub_densityLower_abs_le
    {W n h K y : ℕ} (hWy : W ≤ y) (hKh : K * h ≤ n)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (α β L : ℝ) :
    |roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
      roughHeadDensity W * roughPhysicalLowerFriableMass α β L
        ((2 * n) / row.1) ((2 * n - K * h) / row.1)
          (n / row.1) y| ≤
      roughCanonicalFixedHeadShiftLedger W n h K y α β L row := by
  have hloSplit : n / row.1 ≤ (2 * n - K * h) / row.1 := by
    apply Nat.div_le_div_right
    omega
  have hSplitHi : (2 * n - K * h) / row.1 ≤ (2 * n) / row.1 :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hlower : roughPhysicalLowerFriableMass α β L
        ((2 * n) / row.1) ((2 * n - K * h) / row.1)
          (n / row.1) y =
      roughSmoothPhysicalBlock
        (n / row.1) ((2 * n - K * h) / row.1)
          ((2 * n) / row.1) y α (β / L) := by
    simpa only [roughPhysicalLowerFriableMass] using
      (roughSmoothPhysicalBlock_eq_friableEndpoints
        (alpha := α) (broad := β / L) hloSplit hSplitHi).symm
  rw [hlower]
  simpa only [roughCanonicalFixedHeadShiftLedger] using
    roughHeadCompatibleRawRowMass_sub_densityPhysicalBlock_abs_le
      hWy row α β L

/-- The canonical row sum of the head-compatible raw weight is exactly the
ambient raw row mass.  This is the literal bridge from the finite point to
the canonical row type consumed by exactification. -/
theorem sum_canonicalCompleteRoughRowSet_rawWeight_eq_rawRowMass
    (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    ∑ a ∈ rowSet
        (canonicalCompleteRoughRow y (roughRawCandidateSet n h K)) row,
      roughHeadCompatibleRawWeight W n h K α β L
        (canonicalCompleteRoughCandidateValue
          (roughRawCandidateSet n h K) a) =
      roughHeadCompatibleRawRowMass W n h K y row.1 α β L := by
  simpa only [roughHeadCompatibleRawRowMass] using
    sum_canonicalCompleteRoughRowSet_eq_sum_completeRoughRowFiber
      y (roughRawCandidateSet n h K)
        (roughHeadCompatibleRawWeight W n h K α β L) row



/-- Ambient form of the canonical quota error. -/
theorem roughCanonicalRawRowQuotaError_eq_target_sub_rawRowMass
    (W n h K y : ℕ) (α β L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    roughCanonicalRawRowQuotaError W n h K y α β L row =
      (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) -
        roughHeadCompatibleRawRowMass W n h K y row.1 α β L := by
  rw [roughCanonicalRawRowQuotaError,
    sum_canonicalCompleteRoughRowSet_rawWeight_eq_rawRowMass]



/-- With the exact upper endpoint identification, the discrepancy between
the literal canonical quota error and the four-endpoint analytic block is
exactly the fixed-head physical-shift discrepancy. -/
theorem roughCanonicalRawRowQuotaError_sub_physicalFriableCombination_abs
    {W n h K y : ℕ} {α β L δ : ℝ}
    {Xplus X Xminus Xhalf : ℕ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hupper : (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      (FriableAsymptotic.friableCount Xplus y : ℝ) -
        (FriableAsymptotic.friableCount X y : ℝ)) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row -
        roughPhysicalFriableCombination δ α β L
          Xplus X Xminus Xhalf y| =
      |roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
        δ * roughPhysicalLowerFriableMass
          α β L X Xminus Xhalf y| := by
  rw [roughCanonicalRawRowQuotaError_eq_target_sub_rawRowMass,
    hupper, roughPhysicalFriableCombination, Fin.sum_univ_four]
  unfold roughPhysicalLowerFriableMass
  change
    |(((FriableAsymptotic.friableCount Xplus y : ℝ) -
          (FriableAsymptotic.friableCount X y : ℝ)) -
        roughHeadCompatibleRawRowMass W n h K y row.1 α β L) -
      (1 * (FriableAsymptotic.friableCount Xplus y : ℝ) +
        (-(1 + δ * α)) *
          (FriableAsymptotic.friableCount X y : ℝ) +
        δ * (α - β / L) *
          (FriableAsymptotic.friableCount Xminus y : ℝ) +
        δ * (β / L) *
          (FriableAsymptotic.friableCount Xhalf y : ℝ))| =
      |roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
        δ * (α *
          ((FriableAsymptotic.friableCount X y : ℝ) -
            (FriableAsymptotic.friableCount Xminus y : ℝ)) +
        (β / L) *
          ((FriableAsymptotic.friableCount Xminus y : ℝ) -
            (FriableAsymptotic.friableCount Xhalf y : ℝ)))|
  rw [show
    (((FriableAsymptotic.friableCount Xplus y : ℝ) -
          (FriableAsymptotic.friableCount X y : ℝ)) -
        roughHeadCompatibleRawRowMass W n h K y row.1 α β L) -
      (1 * (FriableAsymptotic.friableCount Xplus y : ℝ) +
        (-(1 + δ * α)) *
          (FriableAsymptotic.friableCount X y : ℝ) +
        δ * (α - β / L) *
          (FriableAsymptotic.friableCount Xminus y : ℝ) +
        δ * (β / L) *
          (FriableAsymptotic.friableCount Xhalf y : ℝ)) =
      -(roughHeadCompatibleRawRowMass W n h K y row.1 α β L -
        δ * (α *
          ((FriableAsymptotic.friableCount X y : ℝ) -
            (FriableAsymptotic.friableCount Xminus y : ℝ)) +
        (β / L) *
          ((FriableAsymptotic.friableCount Xminus y : ℝ) -
            (FriableAsymptotic.friableCount Xhalf y : ℝ)))) by ring,
    abs_neg]

/-- Selector-facing paper-scale closure.  The conclusion is about the
literal canonical-row quota error, while all HT--Saias work is delegated to
the weighted four-endpoint theorem.  The fixed-head shift is a third,
separate allowance and is not silently dropped. -/
theorem roughCanonicalRawRowQuotaError_abs_le_of_saiasPaperScale
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L δ mainAllowance transitionAllowance headAllowance : ℝ}
    {Xplus X Xminus Xhalf : ℕ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hupper : (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      (FriableAsymptotic.friableCount Xplus y : ℝ) -
        (FriableAsymptotic.friableCount X y : ℝ))
    (hhead : |roughHeadCompatibleRawRowMass
        W n h K y row.1 α β L -
      δ * roughPhysicalLowerFriableMass
        α β L X Xminus Xhalf y| ≤ headAllowance)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hlogs : ∀ i : Fin 4,
      Real.log
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger δ α β L
        Xplus X Xminus Xhalf y ≤ mainAllowance)
    (htransition : roughPhysicalSaiasTransitionBudget eta δ α β L
        Xplus X Xminus Xhalf y ≤ transitionAllowance) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤
      mainAllowance + transitionAllowance + headAllowance := by
  have hblock := roughPhysicalFriableCombination_abs_le_of_saiasPaperScale
    hBV happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs
      hmain htransition
  have hdiff :=
    roughCanonicalRawRowQuotaError_sub_physicalFriableCombination_abs
      (W := W) (α := α) (β := β) (L := L) (δ := δ)
      (Xplus := Xplus) (X := X) (Xminus := Xminus) (Xhalf := Xhalf)
      row hupper
  calc
    |roughCanonicalRawRowQuotaError W n h K y α β L row| =
      |(roughCanonicalRawRowQuotaError W n h K y α β L row -
          roughPhysicalFriableCombination δ α β L
            Xplus X Xminus Xhalf y) +
        roughPhysicalFriableCombination δ α β L
          Xplus X Xminus Xhalf y| := by
      congr 1
      ring
    _ ≤ |roughCanonicalRawRowQuotaError W n h K y α β L row -
          roughPhysicalFriableCombination δ α β L
            Xplus X Xminus Xhalf y| +
        |roughPhysicalFriableCombination δ α β L
          Xplus X Xminus Xhalf y| := abs_add_le _ _
    _ ≤ headAllowance +
        (mainAllowance + transitionAllowance) := by
      rw [hdiff]
      exact add_le_add hhead hblock
    _ = mainAllowance + transitionAllowance + headAllowance := by ring

/-- Fully literal endpoint specialization used by the selector.  The four
natural endpoints are the quotient endpoints of
`(2n,2n+h]`, `(2n-Kh,2n]`, and `(n,2n-Kh]` in the canonical row.  Thus the
upper endpoint bridge is discharged by the finite row-to-smooth bijection
above; only the fixed-head allowance and the two paper-scale analytic
allowances remain. -/
theorem roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasPaperScale
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L δ mainAllowance transitionAllowance headAllowance : ℝ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (hhead : |roughHeadCompatibleRawRowMass
        W n h K y row.1 α β L -
      δ * roughPhysicalLowerFriableMass α β L
        ((2 * n) / row.1) ((2 * n - K * h) / row.1)
          (n / row.1) y| ≤ headAllowance)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger δ α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      mainAllowance)
    (htransition : roughPhysicalSaiasTransitionBudget eta δ α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      transitionAllowance) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤
      mainAllowance + transitionAllowance + headAllowance := by
  have hlabel : 0 < row.1 :=
    canonicalCompleteRoughRow_label_pos y
      (roughRawCandidateSet n h K) row
  have hhalf : 0 < n / row.1 := Nat.div_pos hrowN hlabel
  have hHalfMinus : n / row.1 ≤ (2 * n - K * h) / row.1 := by
    apply Nat.div_le_div_right
    omega
  have hMinusX : (2 * n - K * h) / row.1 ≤ (2 * n) / row.1 := by
    exact Nat.div_le_div_right (Nat.sub_le _ _)
  have hXPlus : (2 * n) / row.1 ≤ (2 * n + h) / row.1 := by
    exact Nat.div_le_div_right (by omega)
  exact roughCanonicalRawRowQuotaError_abs_le_of_saiasPaperScale
    hBV row (roughUpperCompleteRoughRowTarget_eq_friableEndpoints row)
      hhead happrox hY hy2 hhalf hHalfMinus hMinusX hXPlus hlogs
      hmain htransition

/-- Canonical selector closure with every finite row and head operation
discharged.  The only remaining estimates are the HT--Saias endpoint
envelope, the deterministic main-ledger allowance, the weighted transition
allowance, and the displayed finite fixed-head block-shift ledger. -/
theorem roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasAndHeadLedger
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L mainAllowance transitionAllowance : ℝ}
    (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      mainAllowance)
    (htransition : roughPhysicalSaiasTransitionBudget eta
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤
      transitionAllowance) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤
      mainAllowance + transitionAllowance +
        roughCanonicalFixedHeadShiftLedger W n h K y α β L row := by
  exact roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasPaperScale
    hBV row hrowN hKh
      (roughHeadCompatibleRawRowMass_sub_densityLower_abs_le
        hWy hKh row α β L)
      happrox hY hy2 hlogs hmain htransition

/-- Finite active-row form.  If the deterministic four-endpoint ledger, the
weighted HT--Saias ledger, and the fixed-head block ledger are each at most
the same paper-scale allowance `E`, then the literal canonical row error is
at most `3*E`.  Taking `E = C_W*(X_R/L^2+1)` is exactly the boxed active-row
estimate in the paper. -/
theorem roughCanonicalRawRowQuotaError_abs_le_three_mul_paperAllowance
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ W n h K y : ℕ}
    {α β L E : ℝ}
    (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (htransition : roughPhysicalSaiasTransitionBudget eta
        (roughHeadDensity W) α β L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (hhead : roughCanonicalFixedHeadShiftLedger
        W n h K y α β L row ≤ E) :
    |roughCanonicalRawRowQuotaError W n h K y α β L row| ≤ 3 * E := by
  have h :=
    roughCanonicalRawRowQuotaError_abs_le_of_literalSaiasAndHeadLedger
      hBV hWy row hrowN hKh happrox hY hy2 hlogs hmain htransition
  nlinarith

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankBottomPaperComponents -/
section


/-!
# Actual bottom-bank components from the concrete marker matching

The capacity argument deliberately matches the rectangular upper-bound family
consisting of every signed slot and all four bottom rows.  The path belonging
to a small source prime does not use every one of those rows: source `3` uses
only `3→2→1`, and source `2` uses only `2→1`.  This file therefore separates
the full matched family from the literal relevant subfamily before forming any
set of used occurrences.

For every matched request we retain its actual prime marker, the two state
factors in the corresponding row, and its donor occurrence.  A finite set of
occurrence values is used, so in the last two rows the donor and the upper
state are literally one occurrence, rather than two tagged copies.  The only
global input is the already constructed injective marker matching.  All other
claims below are explicit interval, factorization, and large-prime arithmetic.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal relevant subfamily -/





















































/-! ## The deterministic truncated bottom path -/

























/-! ## A realization obtained from the actual matching -/





namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)





























/-! The four paper rows, with the marker made explicit. -/













/-! ## Orientation-aware realized row and slot changes -/























end BankBottomPaperRealization

/-! ## Complete occurrence sets and rough signatures -/









namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)























































end BankBottomPaperRealization

/-! ## Explicit local geometry and collision freedom -/



namespace BankBottomPaperRealization

variable {n M : ℕ} (realization : BankBottomPaperRealization n M)









/-! ## Relevant markers and marker-to-component uniqueness -/



























end BankBottomPaperRealization

/-! ## Cardinality bound for the actual relevant marker set -/







/-! ## Eventual local geometry and the terminal realized family -/

private theorem bankBottom_yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

theorem eventually_bankBottom_six_le_yNat :
    ∀ᶠ n : ℕ in atTop, 6 ≤ yNat n :=
  bankBottom_yNat_tendsto_atTop.eventually (eventually_ge_atTop 6)





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









/-! ## Literal rough-row adapters -/













/-! ## Uniform paper-scale choices -/









/-- The active real scale also makes the label itself uniformly negligible
relative to `n`. -/
theorem roughCanonical_activeLabel_three_mul_le_half
    {n label : Nat} {deltaStar : Real}
    (hn : 0 < n) (hlabel : 0 < label)
    (hactive : (n : Real) ^ deltaStar <=
      2 * (n : Real) / (label : Real))
    (hpower : (12 : Real) <= (n : Real) ^ deltaStar) :
    6 * label <= n := by
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  have hlabelReal : (0 : Real) < label := by exact_mod_cast hlabel
  have hmul := mul_le_mul_of_nonneg_left hactive hlabelReal.le
  have hcancel :
      (label : Real) * (2 * (n : Real) / (label : Real)) =
        2 * (n : Real) := by field_simp [hlabelReal.ne']
  rw [hcancel] at hmul
  have hpowerMul : (12 : Real) * (label : Real) <=
      (label : Real) * (n : Real) ^ deltaStar := by
    calc
      (12 : Real) * (label : Real) = (label : Real) * 12 := by ring
      _ <= (label : Real) * (n : Real) ^ deltaStar :=
        mul_le_mul_of_nonneg_left hpower hlabelReal.le
  have hbound : (12 : Real) * (label : Real) <= 2 * (n : Real) :=
    hpowerMul.trans hmul
  have hbound' : (6 * label : Real) <= (n : Real) := by
    linarith
  exact_mod_cast hbound'













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankAnchorCollisionFree -/
section


/-!
# Collision freedom between the complete central anchors and the actual bank

The large-anchor branch recovers the common prime marker from the complete
rough factorization above `yNat`.  Once the marker is recovered, the guarded
central-cofactor certificate excludes the two incident state cores.

The residual branch uses the more rigid shape
`2^k * p^e`.  A bottom marker is already above the residual cutoff.  For an
ordinary marker, divisibility first forces the residual base prime to be the
marker; its marker valuation is then one, so cancellation would make the
ordinary state core a power of two, contrary to the path certificate.

Donor-only occurrences do not create an extra case: ordinary donors and the
two nonterminal bottom donors lie above `2n`, while terminal bottom donors
are literally their upper endpoint state.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## The two eventual scale separations used by marker recovery -/



/-- The smooth cutoff tends to infinity, exposed here because a fixed anchor
prefix contributes only the cofactors `1,…,2*depth+1`. -/
theorem bankAnchor_yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

theorem eventually_bankAnchor_fixed_le_yNat (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, B ≤ yNat n :=
  bankAnchor_yNat_tendsto_atTop.eventually (eventually_ge_atTop B)





/-! ## Arithmetic collision kernels -/



namespace BankPaperRealization



/-! ## Literal recovery of the incident cores from actual requests -/





















/-! ## Complete finite collision theorem -/





end BankPaperRealization

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughCompactBVTranslation -/
section


/-!
# The compact bounded-variation translation estimate

This file closes the pure real-analysis premise isolated in
`RoughSaiasNormalization.lean`.  If `f` has total variation at most `2` on
`[-5,5]`, then translating `f` by two parameters in `[0,5]` changes its
`L¹([0,5])` norm by at most twice the distance between the parameters.

The proof uses the cumulative signed variation

`V(x) = variationOnFromTo f [-5,5] (-5) x`.

Both `V` and `V-f` are monotone on the compact interval, so all functions
that occur below are interval integrable.  For `a <= b`, pointwise variation
gives

`|f(a-v)-f(b-v)| <= V(b-v)-V(a-v)`.

After translating the two integrals, additivity on adjacent intervals leaves
one interval of length `b-a` at each endpoint.  Monotonicity bounds their
difference by `(b-a) * (V(5)-V(-5))`, which is at most `2*(b-a)`.
-/

open scoped ENNReal Interval

namespace Erdos390.WholePaper

open Set MeasureTheory

noncomputable section



/-- The compact BV translation premise from `RoughSaiasNormalization` is a
theorem, with exactly the constant and ranges used there. -/
theorem roughCompactBVTranslationPrinciple :
    RoughCompactBVTranslationPrinciple := by
  intro f hfvar a b ha hb
  rcases le_total a b with hab | hba
  · calc
      (∫ v in (0 : ℝ)..5, |f (a - v) - f (b - v)|) ≤
          2 * (b - a) :=
        roughCompactBV_translation_le_of_le hfvar ha hb hab
      _ = 2 * |a - b| := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
  · calc
      (∫ v in (0 : ℝ)..5, |f (a - v) - f (b - v)|) =
          ∫ v in (0 : ℝ)..5, |f (b - v) - f (a - v)| := by
        apply intervalIntegral.integral_congr
        intro v _hv
        change |f (a - v) - f (b - v)| = |f (b - v) - f (a - v)|
        exact abs_sub_comm _ _
      _ ≤ 2 * (a - b) :=
        roughCompactBV_translation_le_of_le hfvar hb ha hba
      _ = 2 * |a - b| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hba)]

/-! ## Unconditional forms of the normalization estimates -/

theorem roughSaiasDickmanDerivative_translation_le_two_unconditional
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    (∫ v in (0 : ℝ)..5,
      |roughSaiasDickmanDerivative (a - v) -
        roughSaiasDickmanDerivative (b - v)|) ≤
      2 * |a - b| :=
  roughSaiasDickmanDerivative_translation_le_two
    roughCompactBVTranslationPrinciple ha hb







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperFixedExceptionalChargeAsymptotic -/
section


/-!
# Asymptotic package for the fixed exceptional low-prime charge

This file records the constants and scale arithmetic used after the finite
weighted Selberg decomposition of `G_fix` has been proved.  In the notation
of the paper,

* `paperExceptionalSelbergMainConstant` is `C_S`;
* `paperExceptionalSelbergRemainderConstant` is `C_R`;
* `paperExceptionalChargeConstant c` is `A_exc(c)`;
* `paperExceptionalChargeEpsilon deltaStar n` is the normalized
  endpoint/remainder coefficient.

The finite majorant below is obtained by composing the separate finite
rough/smooth-fibre argument with the elementary valuation-prefix estimates.
Nothing in this file assumes that the actual exceptional charge satisfies
that majorant.  We prove the finite charge bound and its analytic packaging,
together with the independent arithmetic support fact that, under the
displayed paper-range hypotheses, the actual low-prime charge is exactly
zero above twice the paper's literal real exceptional cutoff.  The
corresponding safe integral-cutoff statement is retained as a corollary.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Auditable paper constants -/

















/-! ## The finite Selberg output and its normalized remainder -/











/-! ## The endpoint remainder tends to zero -/





/-! ## Uniform packaging of the finite majorant -/

/-- Eventually the literal tail ceiling is at most `2cN`. -/
theorem eventually_upperTailLength_cast_le_two_mul_secondOrderScale
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) ≤
        2 * c * secondOrderScale n := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) / secondOrderScale n ≤
        2 * c :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_le_nhds (by linarith : c < 2 * c))
  filter_upwards [hratio, eventually_secondOrderScale_pos] with n hn hscale
  exact (div_le_iff₀ hscale).mp hn







/-! ## Exact support cutoff for the actual fixed charge -/







/-! ## Closing the finite weighted Selberg estimate -/













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasRightAbel -/
section


/-!
# Abel summation with a right derivative

The Dickman test function used in the de Bruijn--Saias Stieltjes
functional is continuous, but it has a corner when its logarithmic
coordinate is `1`.  The usual `sum_mul_eq_sub_sub_integral_mul` asks for a
two-sided derivative at every point of the closed interval and therefore
does not apply literally.

This file records the exact variant needed here.  Its proof follows the
unit-cell proof of Mathlib's Abel summation theorem, replacing the ordinary
FTC on a cell by `integral_eq_sub_of_hasDeriv_right_of_le`.  A single corner
(or indeed finitely many corners) is harmless as long as the displayed
right derivative exists and is integrable.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Finset MeasureTheory Set

noncomputable section

namespace RoughSaiasRightAbel

variable (c : ℕ → ℝ)

/-! ## Unit-cell facts -/

private theorem prefix_eq_on_unit_cell {m n : ℕ} :
    ∀ᵐ t : ℝ, t ∈ Set.Icc (n : ℝ) (n + 1) →
      ∑ k ∈ Finset.Icc m ⌊t⌋₊, c k =
        ∑ k ∈ Finset.Icc m n, c k := by
  filter_upwards [MeasureTheory.Ico_ae_eq_Icc] with t ht hmem
  rw [Nat.floor_eq_on_Ico _ _ (ht.mpr hmem)]

private theorem right_integral_mul_prefix
    {f f' : ℝ → ℝ} {a b t₁ t₂ : ℝ} {n : ℕ}
    (_hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_right : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (f' t) (Set.Ioi t) t)
    (hf'_int : IntegrableOn f' (Set.Icc a b))
    (ht : t₁ ≤ t₂) (hn₁ : (n : ℝ) ≤ t₁)
    (ht₂n : t₂ ≤ (n : ℝ) + 1)
    (hat₁ : a ≤ t₁) (ht₂b : t₂ ≤ b) :
    (∫ t in t₁..t₂,
        f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      (f t₂ - f t₁) * ∑ k ∈ Finset.Icc 0 n, c k := by
  have hcell : Set.uIoc t₁ t₂ ⊆ Set.Icc (n : ℝ) (n + 1) := by
    rw [Set.uIoc_of_le ht]
    exact Set.Ioc_subset_Icc_self.trans
      (Set.Icc_subset_Icc hn₁ ht₂n)
  have hsub : Set.Icc t₁ t₂ ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc hat₁ ht₂b
  have hftc : (∫ t in t₁..t₂, f' t) = f t₂ - f t₁ := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    · exact hf_cont.mono hsub
    · intro t htOpen
      exact hf_right t
        ⟨hat₁.trans_lt htOpen.1, htOpen.2.trans_le ht₂b⟩
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht]
      exact hf'_int.mono_set hsub
  rw [← hftc, ← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [prefix_eq_on_unit_cell c (m := 0) (n := n)] with t hpref htmem
  rw [hpref (hcell htmem)]

private theorem left_floor_bounds {a b : ℝ} {k : ℕ}
    (hk : k ∈ Set.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b := by
  constructor
  · have hkleft := (Set.mem_Ico.mp hk).1
    exact le_of_lt ((Nat.floor_lt' (by omega)).mp hkleft)
  · rw [← Nat.cast_add_one, ← Nat.le_floor_iff' (Nat.succ_ne_zero k)]
    exact (Set.mem_Ico.mp hk).2

private theorem left_floor_bounds_finset {a b : ℝ} {k : ℕ}
    (hk : k ∈ Finset.Ico (⌊a⌋₊ + 1) ⌊b⌋₊) :
    a ≤ k ∧ k + 1 ≤ b := by
  exact left_floor_bounds (by simpa only [← Finset.coe_Ico] using hk)

/-! ## The right-derivative Abel identity -/

/-- Abel summation on a compact real interval for a continuous test
function with an integrable right derivative.  This differs from
`sum_mul_eq_sub_sub_integral_mul` only in the regularity datum. -/
theorem sum_mul_eq_sub_sub_integral_mul_right
    {f f' : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_right : ∀ t ∈ Set.Ioo a b,
      HasDerivWithinAt f (f' t) (Set.Ioi t) t)
    (hf'_int : IntegrableOn f' (Set.Icc a b)) :
    (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k) =
      f b * (∑ k ∈ Finset.Icc 0 ⌊b⌋₊, c k) -
        f a * (∑ k ∈ Finset.Icc 0 ⌊a⌋₊, c k) -
        ∫ t in Set.Ioc a b,
          f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
  rw [← intervalIntegral.integral_of_le hab]
  have haFloor : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
  have hbCeil : b ≤ (⌊b⌋₊ : ℝ) + 1 :=
    (Nat.lt_floor_add_one _).le
  obtain hfloorEq | hfloorLt :=
      eq_or_lt_of_le (Nat.floor_le_floor hab)
  · rw [hfloorEq, Finset.Ioc_eq_empty_of_le le_rfl, Finset.sum_empty,
      ← sub_mul,
      right_integral_mul_prefix c hab hf_cont hf_right hf'_int
        hab (hfloorEq ▸ haFloor) hbCeil le_rfl le_rfl,
      sub_self]
  · have haSucc : a ≤ (⌊a⌋₊ : ℝ) + 1 :=
      (Nat.lt_floor_add_one _).le
    have haSuccB : (⌊a⌋₊ : ℝ) + 1 ≤ b := by
      rw [← Nat.cast_add_one, ← Nat.le_floor_iff (ha.trans hab)]
      exact hfloorLt
    have hbFloor : (⌊b⌋₊ : ℝ) ≤ b :=
      Nat.floor_le (ha.trans hab)
    have haFloorB : a ≤ (⌊b⌋₊ : ℝ) :=
      (Nat.floor_lt ha).mp hfloorLt |>.le
    simp_rw [← smul_eq_mul,
      Finset.sum_Ioc_by_parts (fun k ↦ f k) _ hfloorLt,
      Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc,
      smul_eq_mul]
    have hcells :
        (∑ k ∈ Finset.Ioc ⌊a⌋₊ (⌊b⌋₊ - 1),
            (f ((k + 1 : ℕ) : ℝ) - f k) *
              ∑ n ∈ Finset.Icc 0 k, c n) =
          ∑ k ∈ Finset.Ico (⌊a⌋₊ + 1) ⌊b⌋₊,
            ∫ t in (k : ℝ)..(k + 1 : ℕ),
              f' t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n := by
      rw [← Finset.Ico_add_one_add_one_eq_Ioc,
        Nat.sub_add_cancel (by omega), Eq.comm]
      apply Finset.sum_congr rfl
      intro k hk
      have hkBounds := left_floor_bounds_finset (a := a) (b := b) hk
      exact right_integral_mul_prefix c
        (t₁ := (k : ℝ)) (t₂ := ((k + 1 : ℕ) : ℝ)) (n := k)
        hab hf_cont hf_right hf'_int
        (by exact_mod_cast k.le_succ) le_rfl
        (by norm_num) hkBounds.1
        (by simpa only [Nat.cast_add, Nat.cast_one] using hkBounds.2)
    rw [hcells,
      intervalIntegral.sum_integral_adjacent_intervals_Ico hfloorLt,
      Nat.cast_add, Nat.cast_one,
      ← intervalIntegral.integral_interval_sub_left
        (a := a) (c := (⌊a⌋₊ : ℝ) + 1),
      ← intervalIntegral.integral_add_adjacent_intervals
        (b := (⌊b⌋₊ : ℝ)) (c := b),
      right_integral_mul_prefix c hab hf_cont hf_right hf'_int
        haSucc haFloor le_rfl le_rfl haSuccB,
      right_integral_mul_prefix c hab hf_cont hf_right hf'_int
        hbFloor le_rfl hbCeil haFloorB le_rfl]
    · ring
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le haFloorB]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_right hbFloor)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hbFloor]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_left haFloorB)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le haFloorB]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_right hbFloor)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le haSucc]
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc_right haSuccB)
    · intro k hk
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le
        (by exact_mod_cast k.le_succ)]
      have hkBounds := left_floor_bounds (a := a) (b := b) hk
      have hkUpper : (((k + 1 : ℕ) : ℝ) ≤ b) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hkBounds.2
      exact (integrableOn_mul_sum_Icc c ha hf'_int).mono_set
        (Set.Icc_subset_Icc hkBounds.1 hkUpper)

/-- Natural-endpoint form of the right-derivative Abel identity. -/
theorem sum_mul_eq_sub_sub_integral_mul_right'
    {f f' : ℝ → ℝ} {n m : ℕ} (hnm : n ≤ m)
    (hf_cont : ContinuousOn f (Set.Icc (n : ℝ) m))
    (hf_right : ∀ t ∈ Set.Ioo (n : ℝ) m,
      HasDerivWithinAt f (f' t) (Set.Ioi t) t)
    (hf'_int : IntegrableOn f' (Set.Icc (n : ℝ) m)) :
    (∑ k ∈ Finset.Ioc n m, f k * c k) =
      f m * (∑ k ∈ Finset.Icc 0 m, c k) -
        f n * (∑ k ∈ Finset.Icc 0 n, c k) -
        ∫ t in Set.Ioc (n : ℝ) m,
          f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
  simpa only [Nat.floor_natCast] using
    (sum_mul_eq_sub_sub_integral_mul_right c
      (a := (n : ℝ)) (b := (m : ℝ))
      n.cast_nonneg (Nat.cast_le.mpr hnm) hf_cont hf_right hf'_int)

end RoughSaiasRightAbel

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasStieltjesKernel -/
section


/-!
# The compact Dickman kernel for the de Bruijn signed functional

This file isolates the only nonsmooth point in the integration-by-parts
identification of the Saias normal form.  The repository's finite Dickman
function is `1` to the left of the first face, so its right derivative as a
function of the Stieltjes variable is zero when the logarithmic coordinate
is exactly `1`.  This is different at one point from
`roughSaiasDickmanDerivative`, whose value at `1` is the *Dickman-coordinate*
right limit `-1`.

The open-face representative below has value zero at that corner.  It gives
an honest right derivative for the Stieltjes test function; changing it back
to `roughSaiasDickmanDerivative` later is an almost-everywhere, one-point
change.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section





theorem roughSaiasOpenFaceDickmanDerivative_of_one_lt
    {u : ℝ} (hu : 1 < u) :
    roughSaiasOpenFaceDickmanDerivative u = -rho (u - 1) / u := by
  simp [roughSaiasOpenFaceDickmanDerivative, not_le.mpr hu]



/-- Away from the single corner, the open-face and right-limit
representatives agree pointwise. -/
theorem roughSaiasOpenFaceDickmanDerivative_eq_roughSaias
    {u : ℝ} (hu : u ≠ 1) :
    roughSaiasOpenFaceDickmanDerivative u =
      roughSaiasDickmanDerivative u := by
  rcases lt_or_gt_of_ne hu with hu1 | h1u
  · rw [roughSaiasOpenFaceDickmanDerivative_of_le_one hu1.le,
      roughSaiasDickmanDerivative_of_lt_one hu1]
  · rw [roughSaiasOpenFaceDickmanDerivative_of_one_lt h1u,
      roughSaiasDickmanDerivative_of_one_le h1u.le]

theorem measurable_roughSaiasOpenFaceDickmanDerivative :
    Measurable roughSaiasOpenFaceDickmanDerivative := by
  unfold roughSaiasOpenFaceDickmanDerivative
  apply Measurable.ite measurableSet_Iic measurable_const
  exact (continuous_rho.measurable.comp
    (measurable_id.sub_const 1)).neg.div measurable_id

/-- The open-face representative has the same unit bound as the
right-limit representative on the compact five-face range. -/
theorem roughSaiasOpenFaceDickmanDerivative_abs_le_one
    {u : ℝ} (hu5 : u ≤ 5) :
    |roughSaiasOpenFaceDickmanDerivative u| ≤ 1 := by
  by_cases hu1 : u ≤ 1
  · simp [roughSaiasOpenFaceDickmanDerivative_of_le_one hu1]
  · have h1u : 1 < u := lt_of_not_ge hu1
    have hb := FriableAsymptotic.rho_delay_integrand_bounds h1u.le hu5
    rw [roughSaiasOpenFaceDickmanDerivative_of_one_lt
        h1u, neg_div, abs_neg, abs_of_nonneg hb.1]
    exact hb.2



/-! ## Real logarithmic coordinate and Stieltjes test function -/







/-- On `1 ≤ t ≤ x`, the Stieltjes coordinate stays between zero and
the endpoint coordinate. -/
theorem roughSaiasStieltjesCoordinate_mem
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x) :
    0 ≤ roughSaiasStieltjesCoordinate x y t ∧
      roughSaiasStieltjesCoordinate x y t ≤
        Real.log x / Real.log y := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hxpos : 0 < x := htpos.trans_le htx
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogtx : Real.log t ≤ Real.log x :=
    Real.log_le_log htpos htx
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  unfold roughSaiasStieltjesCoordinate
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlogtx) hlogy.le
  · apply (div_le_iff₀ hlogy).2
    have hendpoint :
        Real.log x / Real.log y * Real.log y = Real.log x := by
      field_simp [hlogy.ne']
    rw [hendpoint]
    linarith

/-- Continuity of the Stieltjes test on every positive compact interval. -/
theorem continuousOn_roughSaiasStieltjesTest
    {x y A B : ℝ} (hy : 1 < y) (hA : 0 < A) :
    ContinuousOn (roughSaiasStieltjesTest x y) (Set.Icc A B) := by
  intro t ht
  have htpos : 0 < t := hA.trans_le ht.1
  have ht0 : t ≠ 0 := htpos.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have hcoord : ContinuousAt (roughSaiasStieltjesCoordinate x y) t := by
    unfold roughSaiasStieltjesCoordinate
    exact (continuousAt_const.sub (Real.continuousAt_log ht0)).div_const _
  unfold roughSaiasStieltjesTest
  exact ((continuousAt_const.mul
      (continuous_rho.continuousAt.comp hcoord)).div
        continuousAt_id ht0).continuousWithinAt

/-! ## The corner-safe right derivative -/

/-- The displayed derivative is the genuine right derivative throughout
the compact Stieltjes interval.  At coordinate `1`, increasing `t` moves
onto the constant Dickman face, hence the zero open-face value above. -/
theorem hasDerivWithinAt_roughSaiasStieltjesTest_right
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    HasDerivWithinAt (roughSaiasStieltjesTest x y)
      (roughSaiasStieltjesTestRightDerivative x y t)
      (Set.Ioi t) t := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have ht0 : t ≠ 0 := htpos.ne'
  have hxpos : 0 < x := htpos.trans_le htx
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hcoordMem := roughSaiasStieltjesCoordinate_mem hy ht1 htx
  have hcoord5 : roughSaiasStieltjesCoordinate x y t ≤ 5 :=
    hcoordMem.2.trans hu5
  by_cases hface : roughSaiasStieltjesCoordinate x y t ≤ 1
  · have heq :
        roughSaiasStieltjesTest x y =ᶠ[nhdsWithin t (Set.Ioi t)]
          (fun s : ℝ ↦ x / s) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hts : t < s := hs
      have hspos : 0 < s := htpos.trans hts
      have hlogts : Real.log t < Real.log s :=
        Real.strictMonoOn_log htpos hspos hts
      have hcoordLt :
          roughSaiasStieltjesCoordinate x y s <
            roughSaiasStieltjesCoordinate x y t := by
        unfold roughSaiasStieltjesCoordinate
        exact (div_lt_div_iff_of_pos_right hlogy).2 (by linarith)
      rw [roughSaiasStieltjesTest,
        rho_eq_one_of_le_one (hcoordLt.le.trans hface)]
      ring
    have hsimple : HasDerivAt (fun s : ℝ ↦ x / s) (-x / t ^ 2) t := by
      have h := (hasDerivAt_const t x).div (hasDerivAt_id t) ht0
      convert h using 1
      simp only [id_eq, zero_mul, mul_one, zero_sub]
    have hvalue : roughSaiasStieltjesTest x y t = x / t := by
      rw [roughSaiasStieltjesTest, rho_eq_one_of_le_one hface]
      ring
    have hcongr := hsimple.hasDerivWithinAt.congr_of_eventuallyEq
      heq hvalue
    convert hcongr using 1
    unfold roughSaiasStieltjesTestRightDerivative
    simp only [roughSaiasOpenFaceDickmanDerivative_of_le_one hface,
      mul_zero, zero_mul, zero_div, rho_eq_one_of_le_one hface,
      mul_one, zero_sub]
    ring
  · have hface' : 1 < roughSaiasStieltjesCoordinate x y t :=
      lt_of_not_ge hface
    have hcoordDeriv :
        HasDerivAt (roughSaiasStieltjesCoordinate x y)
          (-1 / (t * Real.log y)) t := by
      unfold roughSaiasStieltjesCoordinate
      have h := ((hasDerivAt_const t (Real.log x)).sub
        (Real.hasDerivAt_log ht0)).div_const (Real.log y)
      convert h using 1
      field_simp [ht0, hlogy.ne']
      ring
    have hrho : HasDerivAt
        (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
        ((-rho (roughSaiasStieltjesCoordinate x y t - 1) /
            roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y))) t :=
      (hasDerivAt_rho hface' (hcoord5.trans (by norm_num))).comp t hcoordDeriv
    have hquot := ((hasDerivAt_const t x).mul hrho).div
      (hasDerivAt_id t) ht0
    convert hquot.hasDerivWithinAt using 1
    unfold roughSaiasStieltjesTestRightDerivative
    rw [roughSaiasOpenFaceDickmanDerivative_of_one_lt hface']
    simp only [id_eq, Pi.mul_apply, zero_mul, zero_add, mul_one]
    field_simp [ht0]

/-- The right-derivative theorem in the exact open-interval shape expected
by `sum_mul_eq_sub_sub_integral_mul_right`. -/
theorem roughSaiasStieltjesTest_hasRightDerivOn
    {x y R : ℝ} (hy : 1 < y) (_hR : 1 ≤ R) (hRx : R ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    ∀ t ∈ Set.Ioo (1 : ℝ) R,
      HasDerivWithinAt (roughSaiasStieltjesTest x y)
        (roughSaiasStieltjesTestRightDerivative x y t)
        (Set.Ioi t) t := by
  intro t ht
  exact hasDerivWithinAt_roughSaiasStieltjesTest_right hy ht.1.le
    (ht.2.le.trans hRx) hu5

/-! ## Integrability of the right derivative -/

theorem measurable_roughSaiasStieltjesCoordinate (x y : ℝ) :
    Measurable (roughSaiasStieltjesCoordinate x y) := by
  unfold roughSaiasStieltjesCoordinate
  exact (measurable_const.sub Real.measurable_log).div measurable_const

theorem measurable_roughSaiasStieltjesTestRightDerivative
    (x y : ℝ) :
    Measurable (roughSaiasStieltjesTestRightDerivative x y) := by
  have hcoord := measurable_roughSaiasStieltjesCoordinate x y
  unfold roughSaiasStieltjesTestRightDerivative
  exact (((measurable_const.mul
      (measurable_roughSaiasOpenFaceDickmanDerivative.comp hcoord)).mul
        (measurable_const.div
          (measurable_id.mul measurable_const))).div measurable_id).sub
      ((measurable_const.mul (continuous_rho.measurable.comp hcoord)).div
        (measurable_id.pow_const 2))

/-- A crude compact majorant, used only to certify ordinary integrability.
The later sharp estimates retain the signed kernel and do not use this
triangle inequality. -/
theorem roughSaiasStieltjesTestRightDerivative_abs_le
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    |roughSaiasStieltjesTestRightDerivative x y t| ≤
      x * (1 / Real.log y + 1) := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hxpos : 0 < x := htpos.trans_le htx
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hcoord := roughSaiasStieltjesCoordinate_mem hy ht1 htx
  have hcoord5 : roughSaiasStieltjesCoordinate x y t ≤ 5 :=
    hcoord.2.trans hu5
  have hD := roughSaiasOpenFaceDickmanDerivative_abs_le_one hcoord5
  have hrho0 : 0 ≤ rho (roughSaiasStieltjesCoordinate x y t) :=
    (rho_pos_on_zero_five hcoord.1 hcoord5).le
  have hrho1 : rho (roughSaiasStieltjesCoordinate x y t) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hcoord5
  have hdenom : 0 < t * Real.log y := mul_pos htpos hlogy
  have hinvDenom : 1 / (t * Real.log y) ≤ 1 / Real.log y := by
    apply one_div_le_one_div_of_le hlogy
    nlinarith [mul_le_mul_of_nonneg_right ht1 hlogy.le]
  have hfirstNonneg :
      0 ≤ x *
        |roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t)| *
          (1 / (t * Real.log y)) := by positivity
  have hfirst :
      |x * roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)) / t| ≤
        x * (1 / Real.log y) := by
    calc
      _ = (x *
          |roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t)| *
            (1 / (t * Real.log y))) / t := by
          rw [abs_div, abs_mul, abs_mul, neg_div, abs_neg, abs_div,
            abs_one, abs_of_pos hxpos, abs_of_pos hdenom,
            abs_of_pos htpos]
      _ ≤ x *
          |roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t)| *
            (1 / (t * Real.log y)) :=
        div_le_self hfirstNonneg ht1
      _ ≤ x * 1 * (1 / Real.log y) := by
        gcongr
      _ = x * (1 / Real.log y) := by ring
  have hsecond :
      |x * rho (roughSaiasStieltjesCoordinate x y t) / t ^ 2| ≤ x := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hxpos.le hrho0)
      (sq_nonneg t))]
    calc
      x * rho (roughSaiasStieltjesCoordinate x y t) / t ^ 2 ≤
          x * rho (roughSaiasStieltjesCoordinate x y t) :=
        div_le_self (mul_nonneg hxpos.le hrho0) (by nlinarith)
      _ ≤ x * 1 := mul_le_mul_of_nonneg_left hrho1 hxpos.le
      _ = x := mul_one x
  unfold roughSaiasStieltjesTestRightDerivative
  calc
    _ ≤
        |x * roughSaiasOpenFaceDickmanDerivative
              (roughSaiasStieltjesCoordinate x y t) *
            (-1 / (t * Real.log y)) / t| +
          |x * rho (roughSaiasStieltjesCoordinate x y t) / t ^ 2| :=
      abs_sub _ _
    _ ≤ x * (1 / Real.log y) + x := add_le_add hfirst hsecond
    _ = x * (1 / Real.log y + 1) := by ring

/-- The corner-safe derivative is integrable on the entire natural compact
interval needed by the finite signed functional. -/
theorem integrableOn_roughSaiasStieltjesTestRightDerivative
    {X : ℕ} {y : ℝ} (hX1 : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    IntegrableOn
      (roughSaiasStieltjesTestRightDerivative (X : ℝ) y)
      (Set.Icc (1 : ℝ) (X : ℝ)) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hC : 0 ≤ (X : ℝ) * (1 / Real.log y + 1) := by
    have hlogy : 0 < Real.log y := Real.log_pos hy
    positivity
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ (X : ℝ) * (1 / Real.log y + 1))
      volume (1 : ℝ) (X : ℝ) :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable
      (roughSaiasStieltjesTestRightDerivative (X : ℝ) y)
      volume (1 : ℝ) (X : ℝ) := by
    apply hconst.mono_fun'
      (measurable_roughSaiasStieltjesTestRightDerivative
        (X : ℝ) y).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
      have htIoc : t ∈ Set.Ioc (1 : ℝ) (X : ℝ) := by
        simpa [Set.uIoc_of_le hXR] using ht
      exact ⟨htIoc.1.le, htIoc.2⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using
      (roughSaiasStieltjesTestRightDerivative_abs_le
        hy htI.1 htI.2 hu5)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hXR).mp hint

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasContinuousBuchstab -/
section


/-!
# The compact base-free functional behind continuous Buchstab

The de Bruijn approximation has a base-free Stieltjes description against

`d (floor t / t)`.

Since `t \mapsto floor t / t` is not monotone, Mathlib's positive
`StieltjesFunction.measure` is not the right primitive here.  On a finite
interval its signed action is instead represented explicitly as

`sum f(n) / n - integral f(t) floor(t) / t^2 dt`.

This file introduces that atom-minus-density functional, together with the
zero extension of the Dickman function which supplies its exact support.
The cutoff is kept as an explicit natural number: in the continuous
Buchstab identity the outer cutoff can then remain fixed while the first
argument changes from `x` to `x / s`.  The support lemmas below show that
this choice is harmless.

The eventual identification with `roughSaiasLambdaNormalForm` is a separate
finite Abel calculation.  In particular, no equality with the Stieltjes
normalization is built into any definition in this file.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The supported Dickman profile -/





theorem roughSaiasZeroExtendedRho_of_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    roughSaiasZeroExtendedRho u = rho u := by
  simp [roughSaiasZeroExtendedRho, not_lt.mpr hu]



theorem measurable_roughSaiasZeroExtendedRho :
    Measurable roughSaiasZeroExtendedRho := by
  unfold roughSaiasZeroExtendedRho
  apply Measurable.ite measurableSet_Iio measurable_const
  exact continuous_rho.measurable

/-- On the five constructed faces, the supported profile remains in the
unit interval. -/
theorem roughSaiasZeroExtendedRho_mem_unitInterval
    {u : ℝ} (hu5 : u ≤ 5) :
    0 ≤ roughSaiasZeroExtendedRho u ∧
      roughSaiasZeroExtendedRho u ≤ 1 := by
  by_cases hu : u < 0
  · simp [roughSaiasZeroExtendedRho_of_neg hu]
  · have hu0 : 0 ≤ u := le_of_not_gt hu
    rw [roughSaiasZeroExtendedRho_of_nonneg hu0]
    exact ⟨(rho_pos_on_zero_five hu0 hu5).le,
      FriableAsymptotic.rho_le_one_of_le_five hu5⟩





theorem measurable_roughSaiasStieltjesDickmanProfile
    (x y : ℝ) :
    Measurable (roughSaiasStieltjesDickmanProfile x y) := by
  have hquot : Measurable (fun t : ℝ => x / t) :=
    measurable_const.div measurable_id
  have hcoordinate : Measurable
      (fun t : ℝ => Real.log (x / t) / Real.log y) :=
    (Real.measurable_log.comp hquot).div measurable_const
  exact measurable_const.mul
    (measurable_roughSaiasZeroExtendedRho.comp hcoordinate)

/-- The supported profile is exactly zero beyond its first argument. -/
theorem roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (hxt : x < t) :
    roughSaiasStieltjesDickmanProfile x y t = 0 := by
  have hratioPos : 0 < x / t := div_pos hx ht
  have hratioLt : x / t < 1 := (div_lt_one ht).2 hxt
  have hlogRatio : Real.log (x / t) < 0 :=
    Real.log_neg hratioPos hratioLt
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hcoordinate : Real.log (x / t) / Real.log y < 0 :=
    div_neg_of_neg_of_pos hlogRatio hlogy
  unfold roughSaiasStieltjesDickmanProfile
  rw [roughSaiasZeroExtendedRho_of_neg hcoordinate, mul_zero]





/-- On the supported interval, the logarithmic quotient used in this file
is the real coordinate from `RoughSaiasStieltjesKernel`. -/
theorem roughSaiasStieltjesCoordinate_eq_log_div
    {x y t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    roughSaiasStieltjesCoordinate x y t =
      Real.log (x / t) / Real.log y := by
  unfold roughSaiasStieltjesCoordinate
  rw [Real.log_div hx.ne' ht.ne']

/-- Dividing the supported profile by the Stieltjes variable gives exactly
the corner-safe Abel test from `RoughSaiasStieltjesKernel`. -/
theorem roughSaiasStieltjesDickmanProfile_div_eq_test
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (htx : t ≤ x) :
    roughSaiasStieltjesDickmanProfile x y t / t =
      roughSaiasStieltjesTest x y t := by
  have hratio : 1 ≤ x / t := by
    exact (le_div_iff₀ ht).2 (by simpa using htx)
  have hcoordinate :
      0 ≤ Real.log (x / t) / Real.log y :=
    div_nonneg (Real.log_nonneg hratio) (Real.log_pos hy).le
  unfold roughSaiasStieltjesDickmanProfile roughSaiasStieltjesTest
    roughSaiasStieltjesCoordinate
  rw [roughSaiasZeroExtendedRho_of_nonneg hcoordinate,
    Real.log_div hx.ne' ht.ne']

/-- Multiplicative form of the preceding test-profile identification. -/
theorem roughSaiasStieltjesDickmanProfile_eq_mul_test
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (htx : t ≤ x) :
    roughSaiasStieltjesDickmanProfile x y t =
      t * roughSaiasStieltjesTest x y t := by
  have h := roughSaiasStieltjesDickmanProfile_div_eq_test
    hx hy ht htx
  have ht0 : t ≠ 0 := ht.ne'
  calc
    roughSaiasStieltjesDickmanProfile x y t =
        (roughSaiasStieltjesDickmanProfile x y t / t) * t :=
      (div_mul_cancel₀ _ ht0).symm
    _ = t * roughSaiasStieltjesTest x y t := by
      rw [h]
      ring



/-! ## The finite atom-minus-density functional -/



theorem measurable_roughSaiasFloorDensity :
    Measurable roughSaiasFloorDensity := by
  have hfloorNat : Measurable (fun t : ℝ => ⌊t⌋₊) :=
    measurable_id.nat_floor
  have hfloorReal : Measurable (fun t : ℝ => ((⌊t⌋₊ : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hfloorNat
  exact hfloorReal.div (measurable_id.pow_const 2)





















/-! ## Cutoff independence -/

theorem roughSaiasStieltjesAtomPart_eq_of_cutoff
    {R S : ℕ} {f : ℝ → ℝ} (hRS : R ≤ S)
    (hzero : ∀ n, R < n → n ≤ S → f (n : ℝ) = 0) :
    roughSaiasStieltjesAtomPart R f =
      roughSaiasStieltjesAtomPart S f := by
  unfold roughSaiasStieltjesAtomPart
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hRS⟩
  · intro n hnS hnR
    have hnData := Finset.mem_Icc.mp hnS
    have hRn : R < n := by
      by_contra hnot
      apply hnR
      exact Finset.mem_Icc.mpr ⟨hnData.1, le_of_not_gt hnot⟩
    rw [hzero n hRn hnData.2, zero_div]

theorem roughSaiasStieltjesDensityPart_eq_of_cutoff
    {R S : ℕ} {f : ℝ → ℝ} (hRS : R ≤ S)
    (hzero : ∀ t, (R : ℝ) < t → t ≤ (S : ℝ) → f t = 0) :
    roughSaiasStieltjesDensityPart R f =
      roughSaiasStieltjesDensityPart S f := by
  have hsubset : Set.Ioc (1 : ℝ) (R : ℝ) ⊆
      Set.Ioc (1 : ℝ) (S : ℝ) := by
    rintro t ⟨ht1, htR⟩
    exact ⟨ht1, htR.trans (by exact_mod_cast hRS)⟩
  unfold roughSaiasStieltjesDensityPart
  symm
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
    measurableSet_Ioc hsubset
  intro t ht
  have htS := ht.1
  have htNotR := ht.2
  have hRt : (R : ℝ) < t := by
    by_contra hnot
    exact htNotR ⟨htS.1, le_of_not_gt hnot⟩
  rw [hzero t hRt htS.2, zero_mul]

theorem roughSaiasFiniteStieltjesFunctional_eq_of_cutoff
    {R S : ℕ} {f : ℝ → ℝ} (hRS : R ≤ S)
    (hzero : ∀ t, (R : ℝ) < t → t ≤ (S : ℝ) → f t = 0) :
    roughSaiasFiniteStieltjesFunctional R f =
      roughSaiasFiniteStieltjesFunctional S f := by
  have hzeroNat : ∀ n, R < n → n ≤ S → f (n : ℝ) = 0 := by
    intro n hRn hnS
    exact hzero (n : ℝ) (by exact_mod_cast hRn) (by exact_mod_cast hnS)
  unfold roughSaiasFiniteStieltjesFunctional
  rw [roughSaiasStieltjesAtomPart_eq_of_cutoff hRS hzeroNat,
    roughSaiasStieltjesDensityPart_eq_of_cutoff hRS hzero]

/-! ## A real-base de Bruijn functional -/





/-- Once the cap lies above `x`, enlarging it changes neither the atoms nor
the density. -/
theorem roughSaiasLambdaStieltjesWithCutoff_eq_of_le
    {R S : ℕ} {x y : ℝ} (hRS : R ≤ S)
    (hx : 0 < x) (hy : 1 < y) (hxR : x ≤ (R : ℝ)) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjesWithCutoff S x y := by
  unfold roughSaiasLambdaStieltjesWithCutoff
  apply roughSaiasFiniteStieltjesFunctional_eq_of_cutoff hRS
  intro t hRt htS
  have hxt : x < t := hxR.trans_lt hRt
  exact roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
    hx hy (hx.trans hxt) hxt

theorem roughSaiasLambdaStieltjesWithCutoff_eq_canonical
    {R : ℕ} {x y : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hxR : x ≤ (R : ℝ)) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjes x y := by
  have hceilR : ⌈x⌉₊ ≤ R := Nat.ceil_le.mpr hxR
  unfold roughSaiasLambdaStieltjes
  symm
  exact roughSaiasLambdaStieltjesWithCutoff_eq_of_le
    hceilR hx hy (Nat.le_ceil x)

/-- At a positive natural outer endpoint, the atom part is literally the
finite sum of the corner-safe Abel test. -/
theorem roughSaiasStieltjesAtomPart_profile_nat
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y) :
    roughSaiasStieltjesAtomPart X
        (roughSaiasStieltjesDickmanProfile (X : ℝ) y) =
      ∑ n ∈ Finset.Icc 1 X,
        roughSaiasStieltjesTest (X : ℝ) y (n : ℝ) := by
  unfold roughSaiasStieltjesAtomPart
  apply Finset.sum_congr rfl
  intro n hn
  have hnData := Finset.mem_Icc.mp hn
  exact roughSaiasStieltjesDickmanProfile_div_eq_test
    (by exact_mod_cast hX) hy (by exact_mod_cast hnData.1)
      (by exact_mod_cast hnData.2)

/-- Right-derivative Abel summation for the exact atom sum.  This is the
corner-safe integration-by-parts step; the remaining cancellation with the
floor density is kept separate. -/
theorem roughSaiasStieltjesTest_sum_eq_endpoint_sub_integral
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    (∑ n ∈ Finset.Icc 1 X,
        roughSaiasStieltjesTest (X : ℝ) y (n : ℝ)) =
      (X : ℝ) -
        ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
            ((⌊t⌋₊ : ℕ) : ℝ) := by
  have hcont : ContinuousOn
      (roughSaiasStieltjesTest (X : ℝ) y)
      (Set.Icc ((1 : ℕ) : ℝ) (X : ℝ)) :=
    continuousOn_roughSaiasStieltjesTest hy (by norm_num)
  have hright : ∀ t ∈ Set.Ioo ((1 : ℕ) : ℝ) (X : ℝ),
      HasDerivWithinAt (roughSaiasStieltjesTest (X : ℝ) y)
        (roughSaiasStieltjesTestRightDerivative (X : ℝ) y t)
        (Set.Ioi t) t := by
    simpa only [Nat.cast_one] using
      (roughSaiasStieltjesTest_hasRightDerivOn
        (x := (X : ℝ)) (y := y) (R := (X : ℝ))
        hy (by exact_mod_cast hX) le_rfl hu5)
  have hint : IntegrableOn
      (roughSaiasStieltjesTestRightDerivative (X : ℝ) y)
      (Set.Icc ((1 : ℕ) : ℝ) (X : ℝ)) := by
    simpa only [Nat.cast_one] using
      (integrableOn_roughSaiasStieltjesTestRightDerivative hX hy hu5)
  have hAbel :=
    RoughSaiasRightAbel.sum_mul_eq_sub_sub_integral_mul_right'
      FriableAsymptotic.positiveIncrement
      (f := roughSaiasStieltjesTest (X : ℝ) y)
      (f' := roughSaiasStieltjesTestRightDerivative (X : ℝ) y)
      (n := 1) (m := X)
      hX hcont hright hint
  have hcum (N : ℕ) :
      (∑ k ∈ Finset.Icc 0 N,
          FriableAsymptotic.positiveIncrement k) = (N : ℝ) := by
    have hfin : Finset.Icc 0 N = Finset.range (N + 1) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_range]
      omega
    rw [hfin]
    exact FriableAsymptotic.sum_range_positiveIncrement N
  have hweighted :
      (∑ k ∈ Finset.Ioc 1 X,
          roughSaiasStieltjesTest (X : ℝ) y (k : ℝ) *
            FriableAsymptotic.positiveIncrement k) =
        ∑ k ∈ Finset.Ioc 1 X,
          roughSaiasStieltjesTest (X : ℝ) y (k : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      rw [Finset.mem_Ioc] at hk
      omega
    simp [FriableAsymptotic.positiveIncrement, hk0]
  rw [hweighted] at hAbel
  simp_rw [hcum] at hAbel
  rw [roughSaiasStieltjesTest_self
      (x := (X : ℝ)) (y := y) (by exact_mod_cast (show X ≠ 0 by omega))]
    at hAbel
  nth_rewrite 1 [Finset.Icc_eq_cons_Ioc hX]
  rw [Finset.sum_cons, hAbel]
  ring

/-- Expansion of the capped real-base functional at a natural outer
endpoint into the Abel test sum and its floor density. -/
theorem roughSaiasLambdaStieltjesWithCutoff_nat_eq_test_sub_density
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y) :
    roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) y =
      (∑ n ∈ Finset.Icc 1 X,
          roughSaiasStieltjesTest (X : ℝ) y (n : ℝ)) -
        roughSaiasStieltjesDensityPart X
          (roughSaiasStieltjesDickmanProfile (X : ℝ) y) := by
  unfold roughSaiasLambdaStieltjesWithCutoff
    roughSaiasFiniteStieltjesFunctional
  rw [roughSaiasStieltjesAtomPart_profile_nat hX hy]







/-- On a nonnegative Dickman coordinate, the supported profile is a fixed
multiple of the project's ordinary Dickman antiderivative. -/
theorem roughSaiasStieltjesDickmanProfile_eq_mul_antiderivative
    {x y t : ℝ} (ht : 0 < t)
    (hcoordinate : 0 ≤ Real.log (x / t) / Real.log y) :
    roughSaiasStieltjesDickmanProfile x y t =
      t * FriableAsymptotic.dickmanAntiderivative (x / t) y := by
  unfold roughSaiasStieltjesDickmanProfile
    FriableAsymptotic.dickmanAntiderivative
  rw [roughSaiasZeroExtendedRho_of_nonneg hcoordinate]
  field_simp [ht.ne']

/-- In the active region, the pointwise continuous-Buchstab profile is a
fixed multiple of the ordinary Dickman continuous weight. -/
theorem roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
    {x s t : ℝ} (hx : 0 < x) (hs : 1 < s) (ht : 0 < t)
    (hactive : 1 ≤ Real.log (x / t) / Real.log s) :
    roughSaiasContinuousBuchstabProfile x s t =
      t * FriableAsymptotic.dickmanContinuousWeight (x / t) s := by
  have hspos : 0 < s := zero_lt_one.trans hs
  have hqpos : 0 < x / t := div_pos hx ht
  have hlogS : 0 < Real.log s := Real.log_pos hs
  have hquotient : (x / s) / t = (x / t) / s := by
    field_simp [hspos.ne', ht.ne']
  have hcoordinate :
      Real.log ((x / s) / t) / Real.log s =
        Real.log (x / t) / Real.log s - 1 := by
    rw [hquotient, Real.log_div hqpos.ne' hspos.ne']
    field_simp [hlogS.ne']
  have hdelayNonneg :
      0 ≤ Real.log (x / t) / Real.log s - 1 := by
    linarith
  unfold roughSaiasContinuousBuchstabProfile
    roughSaiasStieltjesDickmanProfile
    FriableAsymptotic.dickmanContinuousWeight
  rw [hcoordinate,
    roughSaiasZeroExtendedRho_of_nonneg hdelayNonneg]
  field_simp [hspos.ne', ht.ne', hlogS.ne']

theorem roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
    {x s t : ℝ} (hx : 0 < x) (hs : 1 < s) (ht : 0 < t)
    (hxt : x / s < t) :
    roughSaiasContinuousBuchstabProfile x s t = 0 := by
  unfold roughSaiasContinuousBuchstabProfile
  rw [roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
      (div_pos hx (zero_lt_one.trans hs)) hs ht hxt,
    zero_div]

/-- Below the base, the supported Dickman profile is on its initial face
and is therefore exactly its first argument. -/
theorem roughSaiasStieltjesDickmanProfile_eq_first_of_one_le_ratio
    {x y t : ℝ} (hy : 1 < y)
    (hq1 : 1 ≤ x / t) (hqy : x / t ≤ y) :
    roughSaiasStieltjesDickmanProfile x y t = x := by
  have hqpos : 0 < x / t := zero_lt_one.trans_le hq1
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogq : 0 ≤ Real.log (x / t) := Real.log_nonneg hq1
  have hlogqy : Real.log (x / t) ≤ Real.log y :=
    Real.log_le_log hqpos hqy
  have hcoordinateNonneg :
      0 ≤ Real.log (x / t) / Real.log y :=
    div_nonneg hlogq hlogy.le
  have hcoordinateOne :
      Real.log (x / t) / Real.log y ≤ 1 :=
    (div_le_one hlogy).2 hlogqy
  unfold roughSaiasStieltjesDickmanProfile
  rw [roughSaiasZeroExtendedRho_of_nonneg hcoordinateNonneg,
    rho_eq_one_of_le_one hcoordinateOne, mul_one]

/-- The continuous-Buchstab profile is interval integrable up to its birth
face.  At the top endpoint it agrees with the continuous Dickman weight;
this is why the non-strict active-coordinate lemma is used here. -/
theorem intervalIntegrable_roughSaiasContinuousBuchstabProfile_to_birth
    {x t y : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyq : y < x / t) :
    IntervalIntegrable (roughSaiasContinuousBuchstabProfile x · t)
      volume y (x / t) := by
  have hcontWeight : ContinuousOn
      (FriableAsymptotic.dickmanContinuousWeight (x / t))
      (Set.Icc y (x / t)) :=
    (FriableAsymptotic.continuousOn_dickmanContinuousWeight
      (x / t)).mono (fun s hs => by
        rw [Set.mem_Ioi]
        exact hy.trans_le hs.1)
  have hcont : ContinuousOn
      (fun s => t *
        FriableAsymptotic.dickmanContinuousWeight (x / t) s)
      (Set.Icc y (x / t)) :=
    continuousOn_const.mul hcontWeight
  have hbase := hcont.intervalIntegrable_of_Icc
    (μ := volume) hyq.le
  apply hbase.congr
  intro s hsU
  have hsI : s ∈ Set.Ioc y (x / t) := by
    simpa only [Set.uIoc_of_le hyq.le] using hsU
  have hsone : 1 < s := hy.trans hsI.1
  have hspos : 0 < s := zero_lt_one.trans hsone
  have hlogSQ : Real.log s ≤ Real.log (x / t) :=
    Real.log_le_log hspos hsI.2
  have hactive : 1 ≤ Real.log (x / t) / Real.log s :=
    (one_le_div (Real.log_pos hsone)).2 hlogSQ
  exact (roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
    hx hsone ht hactive).symm

/-- Past the birth face, the continuous-Buchstab profile is interval
integrable (and vanishes away from the excluded left endpoint). -/
theorem intervalIntegrable_roughSaiasContinuousBuchstabProfile_from_birth
    {x t z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hq1 : 1 < x / t) (hqz : x / t ≤ z) :
    IntervalIntegrable (roughSaiasContinuousBuchstabProfile x · t)
      volume (x / t) z := by
  have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ))
      volume (x / t) z := continuous_const.intervalIntegrable _ _
  apply hzero.congr
  intro s hsU
  have hsI : s ∈ Set.Ioc (x / t) z := by
    simpa only [Set.uIoc_of_le hqz] using hsU
  have hsone : 1 < s := hq1.trans hsI.1
  have hspos : 0 < s := zero_lt_one.trans hsone
  have hxsMul : x < s * t := (div_lt_iff₀ ht).mp hsI.1
  have hxs : x / s < t := by
    apply (div_lt_iff₀ hspos).2
    simpa only [mul_comm] using hxsMul
  exact (roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
    hx hsone ht hxs).symm

/-- The integral beyond the birth face vanishes.  The value at the left
endpoint itself is immaterial for the interval integral. -/
theorem roughSaiasContinuousBuchstabProfile_integral_from_birth_eq_zero
    {x t z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hq1 : 1 < x / t) (hqz : x / t ≤ z) :
    (∫ s in (x / t)..z,
      roughSaiasContinuousBuchstabProfile x s t) = 0 := by
  have hcongr :
      (∫ s in (x / t)..z,
        roughSaiasContinuousBuchstabProfile x s t) =
        ∫ _s in (x / t)..z, (0 : ℝ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s
    intro hsU
    have hsI : s ∈ Set.Ioc (x / t) z := by
      simpa only [Set.uIoc_of_le hqz] using hsU
    have hsone : 1 < s := hq1.trans hsI.1
    have hspos : 0 < s := zero_lt_one.trans hsone
    have hxsMul : x < s * t := (div_lt_iff₀ ht).mp hsI.1
    have hxs : x / s < t := by
      apply (div_lt_iff₀ hspos).2
      simpa only [mul_comm] using hxsMul
    exact roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
      hx hsone ht hxs
  simpa using hcongr

/-- Pointwise continuous Buchstab on an interval where the quotient remains
strictly active.  This is exactly the already-proved Dickman FTC, transported
through the fixed Stieltjes variable `t`. -/
theorem roughSaiasStieltjesDickmanProfile_buchstab_active
    {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyz : y ≤ z) (hzActive : z < x / t)
    (hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    roughSaiasStieltjesDickmanProfile x y t =
      roughSaiasStieltjesDickmanProfile x z t -
        ∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hzpos : 0 < z := hypos.trans_le hyz
  have hqpos : 0 < x / t := hzpos.trans hzActive
  have hqone : 1 < x / t := (hy.trans_le hyz).trans hzActive
  have hlogQ : 0 < Real.log (x / t) := Real.log_pos hqone
  have hratio : ∀ s ∈ Set.Icc y z,
      1 < Real.log (x / t) / Real.log s ∧
        Real.log (x / t) / Real.log s ≤ 6 := by
    intro s hsI
    have hspos : 0 < s := hypos.trans_le hsI.1
    have hsone : 1 < s := hy.trans_le hsI.1
    have hlogs : 0 < Real.log s := Real.log_pos hsone
    have hsQ : s < x / t := hsI.2.trans_lt hzActive
    have hlogSQ : Real.log s < Real.log (x / t) :=
      Real.strictMonoOn_log hspos hqpos hsQ
    have hlogYS : Real.log y ≤ Real.log s :=
      Real.log_le_log hypos hsI.1
    constructor
    · exact (one_lt_div hlogs).2 hlogSQ
    · exact (div_le_div_of_nonneg_left hlogQ.le
        (Real.log_pos hy) hlogYS).trans hu6
  have hIntegral := FriableAsymptotic.integral_dickmanContinuousWeight
    (x / t) y z hy hyz hratio
  have hkernel :
      (∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t) =
        t * ∫ s in y..z,
          FriableAsymptotic.dickmanContinuousWeight (x / t) s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hsI
    have hsI' : s ∈ Set.Icc y z := by
      simpa [Set.uIcc_of_le hyz] using hsI
    exact roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
      hx (hy.trans_le hsI'.1) ht (hratio s hsI').1.le
  have hyCoordinate :
      0 ≤ Real.log (x / t) / Real.log y :=
    le_trans (by norm_num) (hratio y ⟨le_rfl, hyz⟩).1.le
  have hzCoordinate :
      0 ≤ Real.log (x / t) / Real.log z :=
    le_trans (by norm_num) (hratio z ⟨hyz, le_rfl⟩).1.le
  rw [roughSaiasStieltjesDickmanProfile_eq_mul_antiderivative
      ht hyCoordinate,
    roughSaiasStieltjesDickmanProfile_eq_mul_antiderivative
      ht hzCoordinate,
    hkernel, hIntegral]
  ring

/-- Pointwise continuous Buchstab when the upper endpoint is exactly the
birth face.  The closed-top Dickman FTC supplies the endpoint case `u = 1`;
no derivative is asserted at that corner. -/
theorem roughSaiasStieltjesDickmanProfile_buchstab_birth
    {x t y : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyq : y < x / t)
    (hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    roughSaiasStieltjesDickmanProfile x y t =
      roughSaiasStieltjesDickmanProfile x (x / t) t -
        ∫ s in y..(x / t),
          roughSaiasContinuousBuchstabProfile x s t := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hqpos : 0 < x / t := hypos.trans hyq
  have hlogQ : 0 < Real.log (x / t) :=
    Real.log_pos (hy.trans hyq)
  have hratio : ∀ s ∈ Set.Icc y (x / t),
      1 ≤ Real.log (x / t) / Real.log s ∧
        Real.log (x / t) / Real.log s ≤ 6 := by
    intro s hsI
    have hspos : 0 < s := hypos.trans_le hsI.1
    have hsone : 1 < s := hy.trans_le hsI.1
    have hlogs : 0 < Real.log s := Real.log_pos hsone
    have hlogSQ : Real.log s ≤ Real.log (x / t) :=
      Real.log_le_log hspos hsI.2
    have hlogYS : Real.log y ≤ Real.log s :=
      Real.log_le_log hypos hsI.1
    constructor
    · exact (one_le_div hlogs).2 hlogSQ
    · exact (div_le_div_of_nonneg_left hlogQ.le
        (Real.log_pos hy) hlogYS).trans hu6
  have hIntegral :=
    FriableAsymptotic.integral_dickmanContinuousWeight_closed_top
      (x / t) y (x / t) hy hyq hratio
  have hkernel :
      (∫ s in y..(x / t),
          roughSaiasContinuousBuchstabProfile x s t) =
        t * ∫ s in y..(x / t),
          FriableAsymptotic.dickmanContinuousWeight (x / t) s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hsI
    have hsI' : s ∈ Set.Icc y (x / t) := by
      simpa [Set.uIcc_of_le hyq.le] using hsI
    exact roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
      hx (hy.trans_le hsI'.1) ht (hratio s hsI').1
  have hyCoordinate :
      0 ≤ Real.log (x / t) / Real.log y :=
    le_trans (by norm_num) (hratio y ⟨le_rfl, hyq.le⟩).1
  have hqCoordinate :
      0 ≤ Real.log (x / t) / Real.log (x / t) :=
    le_trans (by norm_num)
      (hratio (x / t) ⟨hyq.le, le_rfl⟩).1
  rw [roughSaiasStieltjesDickmanProfile_eq_mul_antiderivative
      ht hyCoordinate,
    roughSaiasStieltjesDickmanProfile_eq_mul_antiderivative
      ht hqCoordinate,
    hkernel, hIntegral]
  ring

/-- If the birth face has already been passed at the lower endpoint, both
Dickman profiles agree and the continuous-Buchstab integral is zero. -/
theorem roughSaiasStieltjesDickmanProfile_buchstab_inactive
    {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyz : y ≤ z) (hqy : x / t ≤ y) :
    roughSaiasStieltjesDickmanProfile x y t =
      roughSaiasStieltjesDickmanProfile x z t -
        ∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t := by
  have hz : 1 < z := hy.trans_le hyz
  have hprofiles :
      roughSaiasStieltjesDickmanProfile x y t =
        roughSaiasStieltjesDickmanProfile x z t := by
    by_cases hq1 : x / t < 1
    · have hxt : x < t := (div_lt_one ht).mp hq1
      rw [roughSaiasStieltjesDickmanProfile_eq_zero_of_lt hx hy ht hxt,
        roughSaiasStieltjesDickmanProfile_eq_zero_of_lt hx hz ht hxt]
    · have hq1' : 1 ≤ x / t := le_of_not_gt hq1
      rw [roughSaiasStieltjesDickmanProfile_eq_first_of_one_le_ratio
          hy hq1' hqy,
        roughSaiasStieltjesDickmanProfile_eq_first_of_one_le_ratio
          hz hq1' (hqy.trans hyz)]
  have hIntegral :
      (∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t) = 0 := by
    have hcongr :
        (∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t) =
          ∫ _s in y..z, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with s
      intro hsU
      have hsI : s ∈ Set.Ioc y z := by
        simpa only [Set.uIoc_of_le hyz] using hsU
      have hsone : 1 < s := hy.trans hsI.1
      have hspos : 0 < s := zero_lt_one.trans hsone
      have hqs : x / t < s := hqy.trans_lt hsI.1
      have hxsMul : x < s * t := (div_lt_iff₀ ht).mp hqs
      have hxs : x / s < t := by
        apply (div_lt_iff₀ hspos).2
        simpa only [mul_comm] using hxsMul
      exact roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
        hx hsone ht hxs
    simpa using hcongr
  rw [hprofiles, hIntegral, sub_zero]

/-- Pointwise continuous Buchstab across the birth face.  The integral is
split at `x / t`; its tail is zero and its first piece is the closed-top
identity above. -/
theorem roughSaiasStieltjesDickmanProfile_buchstab_cross_birth
    {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (_hyz : y ≤ z)
    (hyq : y < x / t) (hqz : x / t ≤ z)
    (hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    roughSaiasStieltjesDickmanProfile x y t =
      roughSaiasStieltjesDickmanProfile x z t -
        ∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t := by
  have hq1 : 1 < x / t := hy.trans hyq
  have hbirth := roughSaiasStieltjesDickmanProfile_buchstab_birth
    hx ht hy hyq hu6
  have hprefix :=
    intervalIntegrable_roughSaiasContinuousBuchstabProfile_to_birth
      hx ht hy hyq
  have htail :=
    intervalIntegrable_roughSaiasContinuousBuchstabProfile_from_birth
      hx ht hq1 hqz
  have htailZero :=
    roughSaiasContinuousBuchstabProfile_integral_from_birth_eq_zero
      hx ht hq1 hqz
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hprefix htail
  have hIntegral :
      (∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t) =
        ∫ s in y..(x / t),
          roughSaiasContinuousBuchstabProfile x s t := by
    rw [← hsplit, htailZero, add_zero]
  have hprofile :
      roughSaiasStieltjesDickmanProfile x (x / t) t =
        roughSaiasStieltjesDickmanProfile x z t := by
    rw [roughSaiasStieltjesDickmanProfile_eq_first_of_one_le_ratio
          hq1 hq1.le le_rfl,
      roughSaiasStieltjesDickmanProfile_eq_first_of_one_le_ratio
        (hq1.trans_le hqz) hq1.le hqz]
  rw [hprofile, ← hIntegral] at hbirth
  exact hbirth

/-- The pointwise continuous-Buchstab kernel is interval integrable on the
whole base interval.  This is the regularity input needed before lifting the
pointwise identity through the finite signed functional. -/
theorem intervalIntegrable_roughSaiasContinuousBuchstabProfile
    {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyz : y ≤ z)
    (_hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    IntervalIntegrable (roughSaiasContinuousBuchstabProfile x · t)
      volume y z := by
  by_cases hqy : x / t ≤ y
  · have hzero : IntervalIntegrable (fun _ : ℝ => (0 : ℝ))
        volume y z := continuous_const.intervalIntegrable _ _
    apply hzero.congr
    intro s hsU
    have hsI : s ∈ Set.Ioc y z := by
      simpa only [Set.uIoc_of_le hyz] using hsU
    have hsone : 1 < s := hy.trans hsI.1
    have hspos : 0 < s := zero_lt_one.trans hsone
    have hqs : x / t < s := hqy.trans_lt hsI.1
    have hxsMul : x < s * t := (div_lt_iff₀ ht).mp hqs
    have hxs : x / s < t := by
      apply (div_lt_iff₀ hspos).2
      simpa only [mul_comm] using hxsMul
    exact (roughSaiasContinuousBuchstabProfile_eq_zero_of_lt
      hx hsone ht hxs).symm
  · have hyq : y < x / t := lt_of_not_ge hqy
    by_cases hzq : z < x / t
    · have hqpos : 0 < x / t :=
          (zero_lt_one.trans hy).trans (hyz.trans_lt hzq)
      have hcontWeight : ContinuousOn
          (FriableAsymptotic.dickmanContinuousWeight (x / t))
          (Set.Icc y z) :=
        (FriableAsymptotic.continuousOn_dickmanContinuousWeight
          (x / t)).mono (fun s hs => by
            rw [Set.mem_Ioi]
            exact hy.trans_le hs.1)
      have hcont : ContinuousOn
          (fun s => t *
            FriableAsymptotic.dickmanContinuousWeight (x / t) s)
          (Set.Icc y z) :=
        continuousOn_const.mul hcontWeight
      have hbase := hcont.intervalIntegrable_of_Icc
        (μ := volume) hyz
      apply hbase.congr
      intro s hsU
      have hsI : s ∈ Set.Ioc y z := by
        simpa only [Set.uIoc_of_le hyz] using hsU
      have hsone : 1 < s := hy.trans hsI.1
      have hspos : 0 < s := zero_lt_one.trans hsone
      have hsQ : s < x / t := hsI.2.trans_lt hzq
      have hlogSQ : Real.log s < Real.log (x / t) :=
        Real.strictMonoOn_log hspos hqpos hsQ
      have hactive : 1 ≤ Real.log (x / t) / Real.log s :=
        ((one_lt_div (Real.log_pos hsone)).2 hlogSQ).le
      exact (roughSaiasContinuousBuchstabProfile_eq_mul_dickmanWeight
        hx hsone ht hactive).symm
    · exact
        (intervalIntegrable_roughSaiasContinuousBuchstabProfile_to_birth
          hx ht hy hyq).trans
          (intervalIntegrable_roughSaiasContinuousBuchstabProfile_from_birth
            hx ht (hy.trans hyq) (le_of_not_gt hzq))

/-- Full pointwise continuous Buchstab identity for the supported Dickman
profile.  The face bound is the only finite method-of-steps restriction. -/
theorem roughSaiasStieltjesDickmanProfile_buchstab
    {x t y z : ℝ} (hx : 0 < x) (ht : 0 < t)
    (hy : 1 < y) (hyz : y ≤ z)
    (hu6 : Real.log (x / t) / Real.log y ≤ 6) :
    roughSaiasStieltjesDickmanProfile x y t =
      roughSaiasStieltjesDickmanProfile x z t -
        ∫ s in y..z, roughSaiasContinuousBuchstabProfile x s t := by
  by_cases hqy : x / t ≤ y
  · exact roughSaiasStieltjesDickmanProfile_buchstab_inactive
      hx ht hy hyz hqy
  · have hyq : y < x / t := lt_of_not_ge hqy
    by_cases hzq : z < x / t
    · exact roughSaiasStieltjesDickmanProfile_buchstab_active
        hx ht hy hyz hzq hu6
    · exact roughSaiasStieltjesDickmanProfile_buchstab_cross_birth
        hx ht hy hyz hyq (le_of_not_gt hzq) hu6

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSignedFractionalAbel -/
section


/-!
# Signed fractional correction and finite Abel decomposition for the Saias defect

This file goes one level below
`RoughSaiasReverseNormalFormDefectInvLogSqBound`.  It never assumes a bound
for that defect.  Instead it keeps the quotient fractional correction with
its sign, separates the reverse defect into a continuous normal-form prime
sum and that signed correction, and applies the project's existing finite
theta Abel identity to the continuous prime sum.

The resulting quantitative theorem assumes only a cumulative theta-error
bound.  Its right side is the explicit endpoint-plus-variation ledger for the
Saias theta weight.  Thus the remaining inverse-log-square problem is a
deterministic estimate for the displayed signed Abel center, not a renamed
copy of the original defect bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-! ## One quotient: retain the fractional correction with its sign -/







/-- Natural division is exactly the real quotient minus its fractional
part.  This includes the totalized `m=0` case. -/
theorem roughSaiasRealQuotient_sub_fract_eq_natQuotient
    (X m : ℕ) :
    (X : ℝ) / (m : ℝ) -
        Int.fract ((X : ℝ) / (m : ℝ)) =
      ((X / m : ℕ) : ℝ) := by
  rw [Int.self_sub_fract]
  rw [← natCast_floor_eq_intCast_floor (by positivity)]
  rw [Nat.floor_div_eq_div]

/-- Exact signed quotient correction.  No triangle inequality or absolute
value is used. -/
theorem roughSaiasSignedPrimeFloorCorrection_eq_fractional
    (X m : ℕ) :
    roughSaiasSignedPrimeFloorCorrection X m =
      roughSaiasSignedFractionalCorrectionTerm X m := by
  have hfloor := roughSaiasRealQuotient_sub_fract_eq_natQuotient X m
  unfold roughSaiasSignedPrimeFloorCorrection
    roughSaiasContinuousPrimeNormalForm
    roughSaiasSignedFractionalCorrectionTerm
    roughSaiasLambdaNormalForm roughSaiasNaturalMain
  linear_combination
    (roughSaiasG m
      (Real.log ((X : ℝ) / (m : ℝ)) / Real.log (m : ℝ))) * hfloor

/-! ## The reverse defect as continuous part plus signed correction -/







/-! ## Exact finite theta Abel identity -/

















/-! ## The floor/frac-paired natural theta weight -/





/-- Pointwise pairing: the continuous weight is the natural weight plus the
signed fractional correction. -/
theorem roughSaiasNormalFormThetaWeight_eq_natural_add_fractional
    (X m : ℕ) :
    roughSaiasNormalFormThetaWeight X m =
      roughSaiasNaturalQuotientThetaWeight X m +
        roughSaiasFractionalCorrectionThetaWeight X m := by
  unfold roughSaiasNormalFormThetaWeight
    roughSaiasNaturalQuotientThetaWeight
    roughSaiasFractionalCorrectionThetaWeight
  rw [← roughSaiasSignedPrimeFloorCorrection_eq_fractional]
  unfold
    roughSaiasSignedPrimeFloorCorrection
  ring



/-- The natural theta mass is literally the prime sum in the original
normal-form defect. -/
theorem roughSaiasPrimeThetaWeightedInterval_eq_naturalSum
    (X y Z : ℕ) :
    FriableAsymptotic.primeThetaWeightedInterval
        (roughSaiasNaturalQuotientThetaWeight X) y Z =
      ∑ p ∈ roughReversePrimeInterval y Z,
        roughSaiasNaturalMain (X / p) p := by
  unfold FriableAsymptotic.primeThetaWeightedInterval
    roughReversePrimeInterval
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime : p.Prime :=
    Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hlogp : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hpprime.one_lt))
  rw [roughSaiasNaturalQuotientThetaWeight]
  exact div_mul_cancel₀ _ hlogp



/-- Integer Abel main terms respect the pointwise signed pairing. -/
theorem roughSaiasIntegerAbelMain_normalForm_eq_natural_add_fractional
    {X y Z : ℕ} (hyZ : y < Z) :
    FriableAsymptotic.integerAbelMain
        (roughSaiasNormalFormThetaWeight X) y Z =
      FriableAsymptotic.integerAbelMain
          (roughSaiasNaturalQuotientThetaWeight X) y Z +
        FriableAsymptotic.integerAbelMain
          (roughSaiasFractionalCorrectionThetaWeight X) y Z := by
  rw [FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
    FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
    FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  exact roughSaiasNormalFormThetaWeight_eq_natural_add_fractional X m









/-- Direct exact Abel formula for the original defect, now with every
floor/frac contribution paired inside the natural weight. -/
theorem roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta
    (X y Z : ℕ) :
    roughSaiasReverseNormalFormDefect X y Z =
      roughSaiasNaturalIntegerAbelConsistencyDefect X y Z -
        roughSaiasNaturalThetaErrorTransfer X y Z := by
  unfold roughSaiasReverseNormalFormDefect
    roughSaiasNaturalIntegerAbelConsistencyDefect
    roughSaiasNaturalThetaErrorTransfer
  rw [roughSaiasPrimeThetaWeightedInterval_eq_naturalSum]
  ring



/-! ## Quantitative theta transfer, without a defect-bound premise -/







/-- PNT transfer with the floor and fractional variations already paired.
Again the sole analytic premise is a cumulative theta-error bound. -/
theorem roughSaiasNaturalThetaErrorTransfer_abs_le_pntLedger
    {A C : ℝ} {X₀ X y Z : ℕ}
    (htheta : ∀ T, X₀ ≤ T →
      |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ A))
    (hX₀y : X₀ ≤ y) (hyZ : y < Z) :
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      roughSaiasNaturalThetaPNTLedger A C X y Z := by
  unfold roughSaiasNaturalThetaErrorTransfer
    roughSaiasNaturalThetaPNTLedger
  exact FriableAsymptotic.primeThetaWeightedInterval_pnt_bound
    (roughSaiasNaturalQuotientThetaWeight X) htheta hX₀y hyZ





/-! ## Closed fourth-power theta specialization -/



theorem roughSaiasThetaFourthPowerConstant_pos :
    0 < roughSaiasThetaFourthPowerConstant :=
  (Classical.choose_spec
    (FriableAsymptotic.exists_primeLogSumUpTo_error_bound (4 : ℝ))).1



theorem roughSaiasThetaFourthPower_bound
    (T : ℕ) (hT : roughSaiasThetaFourthPowerCutoff ≤ T) :
    |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
      roughSaiasThetaFourthPowerConstant *
        ((T : ℝ) / Real.log (T : ℝ) ^ (4 : ℝ)) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (FriableAsymptotic.exists_primeLogSumUpTo_error_bound (4 : ℝ))).2)
    T hT





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasBaseChange -/
section


/-!
# Base-free sawtooth coordinates for the Saias correction

The difficult base variation in `roughSaiasG m` contains
`fract(m^v) * m^(-v)`.  This file records the exact substitution `t=m^v`
before any absolute value is taken.  After multiplication by the Jacobian,
the sawtooth is `fract(t)`, independent of `m`; all base dependence is left
in the logarithmic Dickman kernel and the factor `1 / log m`.

This is an exact identity for the finite `[0,5]` integral.  The one-variable
Jacobian theorem is used because its monotone form permits the discontinuous
fractional-part integrand.
-/

open scoped Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section







/-- The transformed coordinate is a single log difference divided by the
base logarithm. -/
theorem roughSaiasBaseFreeDickmanCoordinate_eq_sub_div
    (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeDickmanCoordinate q m t =
      (Real.log (q : ℝ) - Real.log t) / Real.log (m : ℝ) := by
  unfold roughSaiasBaseFreeDickmanCoordinate
  ring













/-- The transformed kernel is supported below the natural quotient scale
`q/m`.  Above that scale the Dickman-derivative argument is strictly below
one.  The statement is pointwise, so no regularity of `fract` is needed. -/
theorem roughSaiasBaseFreeFractionalKernel_eq_zero_of_div_lt
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) {t : ℝ}
    (ht : (q : ℝ) / (m : ℝ) < t) :
    roughSaiasBaseFreeFractionalKernel q m t = 0 := by
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have htpos : 0 < t :=
    (div_pos hqpos hmpos).trans ht
  have hq_lt_tm : (q : ℝ) < t * (m : ℝ) :=
    (div_lt_iff₀ hmpos).mp ht
  have hloglt :
      Real.log (q : ℝ) < Real.log t + Real.log (m : ℝ) := by
    have h := Real.strictMonoOn_log hqpos (mul_pos htpos hmpos) hq_lt_tm
    rwa [Real.log_mul htpos.ne' hmpos.ne'] at h
  have harg :
      Real.log (q : ℝ) / Real.log (m : ℝ) -
          Real.log t / Real.log (m : ℝ) < 1 := by
    rw [← sub_div, div_lt_one (Real.log_pos hmone)]
    linarith
  unfold roughSaiasBaseFreeFractionalKernel
  rw [roughSaiasDickmanDerivative_of_lt_one harg]
  simp







/-- Pointwise Jacobian cancellation for `t=m^v`.  This is the algebraic
heart of the base-free representation and retains the signed sawtooth. -/
theorem roughSaiasBaseFreeFractionalKernel_rpow_mul_jacobian
    {q m : ℕ} (hm2 : 2 ≤ m) (v : ℝ) :
    (Real.log (m : ℝ) * (m : ℝ) ^ v) *
        roughSaiasBaseFreeFractionalKernel q m ((m : ℝ) ^ v) =
      roughSaiasDickmanDerivative
          (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
        roughSaiasFractionalWeight m v := by
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hlogm : Real.log (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hmone)
  have hrpow : (m : ℝ) ^ v ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hmpos v)
  have hcancel :
      v * Real.log (m : ℝ) / Real.log (m : ℝ) = v := by
    field_simp [hlogm]
  unfold roughSaiasBaseFreeFractionalKernel
    roughSaiasFractionalWeight
  rw [Real.log_rpow hmpos, hcancel, Real.rpow_neg hmpos.le]
  field_simp [hlogm, hrpow]



/-- Exact change of variables in the signed Saias correction integral.
Unlike the usual continuous substitution lemma, this proof does not require
continuity of `fract`: monotonicity of `v ↦ m^v` is sufficient. -/
theorem roughSaiasFractionalIntegral_eq_baseFree
    {q m : ℕ} (hm2 : 2 ≤ m) :
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v) =
      roughSaiasBaseFreeFractionalIntegral q m := by
  let f : ℝ → ℝ := fun v => (m : ℝ) ^ v
  let f' : ℝ → ℝ := fun v =>
    Real.log (m : ℝ) * (m : ℝ) ^ v
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hfderiv : ∀ v ∈ Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hmpos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hmone).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hmpos.ne').continuousOn
  have hfimage :
      f '' Icc (0 : ℝ) 5 =
        Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    calc
      f '' Icc (0 : ℝ) 5 = Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
        simp [f]
  have hchange :
      (∫ t in f '' Icc (0 : ℝ) 5,
          roughSaiasBaseFreeFractionalKernel q m t) =
        ∫ v in Icc (0 : ℝ) 5,
          f' v • roughSaiasBaseFreeFractionalKernel q m (f v) :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasBaseFreeFractionalKernel q m)
  have hpoint (v : ℝ) :
      f' v • roughSaiasBaseFreeFractionalKernel q m (f v) =
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v := by
    simpa [f, f', smul_eq_mul] using
      roughSaiasBaseFreeFractionalKernel_rpow_mul_jacobian
        (q := q) hm2 v
  have hu : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  unfold roughSaiasBaseFreeFractionalIntegral
  calc
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v) =
        ∫ v in Icc (0 : ℝ) 5,
          roughSaiasDickmanDerivative
              (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
            roughSaiasFractionalWeight m v := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ v in Icc (0 : ℝ) 5,
          f' v • roughSaiasBaseFreeFractionalKernel q m (f v) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v _hv
      exact (hpoint v).symm
    _ = ∫ t in Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)),
          roughSaiasBaseFreeFractionalKernel q m t := by
      rw [← hfimage]
      exact hchange.symm
    _ = ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q m t := by
      rw [intervalIntegral.integral_of_le hu,
        MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- Integrability of the transformed kernel on its finite interval, obtained
from the already proved integrability of the original Saias integrand and
the same monotone Jacobian. -/
theorem roughSaiasBaseFreeFractionalKernel_intervalIntegrable
    {q m : ℕ} (hm2 : 2 ≤ m)
    (hu5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    IntervalIntegrable (roughSaiasBaseFreeFractionalKernel q m)
      volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
  let f : ℝ → ℝ := fun v => (m : ℝ) ^ v
  let f' : ℝ → ℝ := fun v =>
    Real.log (m : ℝ) * (m : ℝ) ^ v
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hfderiv : ∀ v ∈ Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hmpos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hmone).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hmpos.ne').continuousOn
  have hfimage :
      f '' Icc (0 : ℝ) 5 =
        Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    calc
      f '' Icc (0 : ℝ) 5 = Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
        simp [f]
  have horiginal : IntervalIntegrable
      (fun v : ℝ =>
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v)
      volume 0 5 :=
    roughSaiasIntegrand_intervalIntegrable hm2 hu5
  have horiginalIcc : IntegrableOn
      (fun v : ℝ =>
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v)
      (Icc (0 : ℝ) 5) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      horiginal
  have hjacobianIcc : IntegrableOn
      (fun v : ℝ =>
        f' v • roughSaiasBaseFreeFractionalKernel q m (f v))
      (Icc (0 : ℝ) 5) := by
    apply horiginalIcc.congr_fun _ measurableSet_Icc
    intro v _hv
    simpa [f, f', smul_eq_mul] using
      (roughSaiasBaseFreeFractionalKernel_rpow_mul_jacobian
        (q := q) hm2 v).symm
  have hkernelImage : IntegrableOn
      (roughSaiasBaseFreeFractionalKernel q m)
      (f '' Icc (0 : ℝ) 5) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasBaseFreeFractionalKernel q m)).mpr hjacobianIcc
  rw [hfimage] at hkernelImage
  have hu : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hu).mpr hkernelImage









/-- At a natural quotient, `G_m` is exactly `rho` minus the transformed
base-free-sawtooth integral. -/
theorem roughSaiasG_at_natQuotient_eq_baseFree
    {q m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasG m
        (Real.log (q : ℝ) / Real.log (m : ℝ)) =
      rho (Real.log (q : ℝ) / Real.log (m : ℝ)) -
        roughSaiasBaseFreeFractionalIntegral q m := by
  unfold roughSaiasG
  rw [roughSaiasFractionalIntegral_eq_baseFree hm2]



/-! ## Exact floor/base pairing in the transformed coordinate -/

/-- Natural main term at a fixed quotient, written with the base-free
sawtooth integral. -/
theorem roughSaiasNaturalMain_eq_rho_sub_baseFree
    {q m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasNaturalMain q m =
      (q : ℝ) *
        (rho (Real.log (q : ℝ) / Real.log (m : ℝ)) -
          roughSaiasBaseFreeFractionalIntegral q m) := by
  unfold roughSaiasNaturalMain FriableAsymptotic.dickmanU
  rw [roughSaiasG_at_natQuotient_eq_baseFree hm2]









/-! ## The signed center as a base-free quotient-block sum -/







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasStieltjesNormalForm -/
section


/-!
# Identification of the finite signed functional with the Saias normal form

This file performs the finite integration-by-parts calculation that was
deliberately absent from `RoughSaiasNormalization`.  The atom part is
handled by the corner-safe right-derivative Abel theorem.  Its density term
cancels the quotient-rule part of that derivative before any estimate is
taken.  What remains splits exactly as

* a smooth Dickman FTC term, and
* the signed base-free fractional correction already formalized in
  `RoughSaiasBaseChange`.

Thus the explicit atom-minus-density functional is identified with the
existing normal form at a positive natural endpoint without assuming any
defect or endpoint estimate.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The exact density cancellation -/







theorem roughSaiasNatFloor_cast_eq_sub_fract
    {t : ℝ} (ht : 0 ≤ t) :
    (((⌊t⌋₊ : ℕ) : ℝ)) = t - Int.fract t := by
  rw [Int.self_sub_fract,
    ← natCast_floor_eq_intCast_floor ht]

/-- Pointwise `floor = t - fract` inside the remaining signed kernel. -/
theorem roughSaiasStieltjesFloorCorrection_eq_smooth_sub_fractional
    {X : ℕ} {y t : ℝ} (ht : 0 < t) (hy : 1 < y) :
    roughSaiasStieltjesFloorCorrection X y t =
      roughSaiasStieltjesSmoothCorrection X y t -
        roughSaiasStieltjesFractionalCorrection X y t := by
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have ht0 : t ≠ 0 := ht.ne'
  unfold roughSaiasStieltjesFloorCorrection
    roughSaiasStieltjesSmoothCorrection
    roughSaiasStieltjesFractionalCorrection
  rw [roughSaiasNatFloor_cast_eq_sub_fract ht.le]
  field_simp [ht0, hlogy]

/-- The quotient-rule `rho/t²` term in the right Abel derivative cancels
the entire absolutely continuous floor density. -/
theorem roughSaiasStieltjesDerivativeFloor_add_density
    {X : ℕ} {y t : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (ht : 0 < t) (htX : t ≤ (X : ℝ)) :
    roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
          (((⌊t⌋₊ : ℕ) : ℝ)) +
        roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
          roughSaiasFloorDensity t =
      -roughSaiasStieltjesFloorCorrection X y t := by
  have hXR : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have ht0 : t ≠ 0 := ht.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  rw [roughSaiasStieltjesDickmanProfile_eq_mul_test
    hXR hy ht htX]
  unfold roughSaiasStieltjesTestRightDerivative
    roughSaiasStieltjesTest roughSaiasFloorDensity
    roughSaiasStieltjesFloorCorrection
  field_simp [ht0, hlogy]
  ring

theorem roughSaiasPositiveIncrement_prefix (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 N,
      FriableAsymptotic.positiveIncrement k) = (N : ℝ) := by
  have hfin : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hfin]
  exact FriableAsymptotic.sum_range_positiveIncrement N

/-- Integrability of the derivative-times-floor term follows directly from
the generic Abel-summation integrability lemma. -/
theorem integrableOn_roughSaiasStieltjesDerivative_mul_floor
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦
        roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
          (((⌊t⌋₊ : ℕ) : ℝ)))
      (Set.Ioc (1 : ℝ) (X : ℝ)) := by
  have hint := integrableOn_roughSaiasStieltjesTestRightDerivative
    hX hy hu5
  have hmul := integrableOn_mul_sum_Icc
    FriableAsymptotic.positiveIncrement (a := (1 : ℝ))
      (b := (X : ℝ)) (m := 0) (by norm_num) hint
  have hmul' := hmul.mono_set Set.Ioc_subset_Icc_self
  simpa only [roughSaiasPositiveIncrement_prefix] using hmul'

/-- The density is measurable and bounded by the natural endpoint on its
compact support. -/
theorem integrableOn_roughSaiasStieltjesProfile_mul_floorDensity
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦
        roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
          roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (X : ℝ)) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXnonneg : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hmeas : Measurable (fun t : ℝ ↦
      roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
        roughSaiasFloorDensity t) :=
    (measurable_roughSaiasStieltjesDickmanProfile (X : ℝ) y).mul
      measurable_roughSaiasFloorDensity
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ (X : ℝ))
      volume (1 : ℝ) (X : ℝ) :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable (fun t : ℝ ↦
      roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
        roughSaiasFloorDensity t) volume (1 : ℝ) (X : ℝ) := by
    apply hconst.mono_fun' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
      simpa only [Set.uIcc_of_le hXR] using Set.uIoc_subset_uIcc ht
    have htpos : 0 < t := zero_lt_one.trans_le htI.1
    have hcoord := roughSaiasStieltjesCoordinate_mem hy htI.1 htI.2
    have hcoord5 := hcoord.2.trans hu5
    have hcoordEq := roughSaiasStieltjesCoordinate_eq_log_div
      (x := (X : ℝ)) (y := y) (t := t)
      (by exact_mod_cast (show 0 < X by omega)) htpos
    have hcoordLog5 :
        Real.log ((X : ℝ) / t) / Real.log y ≤ 5 := by
      rw [← hcoordEq]
      exact hcoord5
    have hzeroRho :=
      roughSaiasZeroExtendedRho_mem_unitInterval hcoordLog5
    have hprofile0 : 0 ≤
        roughSaiasStieltjesDickmanProfile (X : ℝ) y t := by
      unfold roughSaiasStieltjesDickmanProfile
      exact mul_nonneg hXnonneg hzeroRho.1
    have hprofileX :
        roughSaiasStieltjesDickmanProfile (X : ℝ) y t ≤ (X : ℝ) := by
      unfold roughSaiasStieltjesDickmanProfile
      exact (mul_le_mul_of_nonneg_left hzeroRho.2 hXnonneg).trans_eq
        (mul_one _)
    have hfloor0 : (0 : ℝ) ≤ (((⌊t⌋₊ : ℕ) : ℝ)) := by
      positivity
    have hfloorLe : (((⌊t⌋₊ : ℕ) : ℝ)) ≤ t :=
      Nat.floor_le htpos.le
    have hdenom : 0 < t ^ 2 := sq_pos_of_pos htpos
    have hdensity0 : 0 ≤ roughSaiasFloorDensity t := by
      unfold roughSaiasFloorDensity
      exact div_nonneg hfloor0 hdenom.le
    have hdensity1 : roughSaiasFloorDensity t ≤ 1 := by
      unfold roughSaiasFloorDensity
      apply (div_le_one hdenom).2
      have hquad : 0 ≤ t * (t - 1) :=
        mul_nonneg htpos.le (sub_nonneg.mpr htI.1)
      exact hfloorLe.trans (by nlinarith)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hprofile0 hdensity0)]
    calc
      roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
          roughSaiasFloorDensity t ≤
        roughSaiasStieltjesDickmanProfile (X : ℝ) y t * 1 :=
          mul_le_mul_of_nonneg_left hdensity1 hprofile0
      _ ≤ (X : ℝ) * 1 :=
        mul_le_mul_of_nonneg_right hprofileX (by norm_num)
      _ = (X : ℝ) := mul_one _
  have hintIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hXR).mp hint
  exact hintIcc.mono_set Set.Ioc_subset_Icc_self

/-- The capped signed functional is the natural endpoint plus the one
remaining signed floor correction. -/
theorem roughSaiasLambdaStieltjesWithCutoff_nat_eq_add_floorCorrection
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) y =
      (X : ℝ) +
        ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          roughSaiasStieltjesFloorCorrection X y t := by
  have hderiv := integrableOn_roughSaiasStieltjesDerivative_mul_floor
    hX hy hu5
  have hdensity := integrableOn_roughSaiasStieltjesProfile_mul_floorDensity
    hX hy hu5
  rw [roughSaiasLambdaStieltjesWithCutoff_nat_eq_test_sub_density hX hy,
    roughSaiasStieltjesTest_sum_eq_endpoint_sub_integral hX hy hu5]
  unfold roughSaiasStieltjesDensityPart
  have hadd := MeasureTheory.integral_add hderiv hdensity
  have hpoint :
      (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          (roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
              (((⌊t⌋₊ : ℕ) : ℝ)) +
            roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
              roughSaiasFloorDensity t)) =
        ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          -roughSaiasStieltjesFloorCorrection X y t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact roughSaiasStieltjesDerivativeFloor_add_density hX hy
      (zero_lt_one.trans ht.1) ht.2
  calc
    (X : ℝ) -
          (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
              (((⌊t⌋₊ : ℕ) : ℝ))) -
          (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
              roughSaiasFloorDensity t) =
        (X : ℝ) -
          ((∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
              roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
                (((⌊t⌋₊ : ℕ) : ℝ))) +
            (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
              roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
                roughSaiasFloorDensity t)) := by ring
    _ = (X : ℝ) -
          ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            (roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
                (((⌊t⌋₊ : ℕ) : ℝ)) +
              roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
                roughSaiasFloorDensity t) := by rw [hadd]
    _ = (X : ℝ) -
          ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            -roughSaiasStieltjesFloorCorrection X y t := by rw [hpoint]
    _ = (X : ℝ) +
          ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            roughSaiasStieltjesFloorCorrection X y t := by
      rw [MeasureTheory.integral_neg]
      ring

/-! ## Evaluation of the smooth part -/

/-- Multiplying the Abel test by `t/x` recovers `rho` and transfers its
corner-safe right derivative to the logarithmic coordinate. -/
theorem hasDerivWithinAt_roughSaiasRhoCoordinate_right
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    HasDerivWithinAt
      (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
      (roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t) *
        (-1 / (t * Real.log y)))
      (Set.Ioi t) t := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have ht0 : t ≠ 0 := htpos.ne'
  have hxpos : 0 < x := htpos.trans_le htx
  have hx0 : x ≠ 0 := hxpos.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have htest := hasDerivWithinAt_roughSaiasStieltjesTest_right
    hy ht1 htx hu5
  have hprod := (hasDerivAt_id t).hasDerivWithinAt.mul htest
  have hquot := hprod.div_const x
  have heq :
      (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
        =ᶠ[nhdsWithin t (Set.Ioi t)]
      (fun s : ℝ ↦ s * roughSaiasStieltjesTest x y s / x) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := htpos.trans hs
    unfold roughSaiasStieltjesTest
    field_simp [hspos.ne', hx0]
  have hvalue :
      rho (roughSaiasStieltjesCoordinate x y t) =
        t * roughSaiasStieltjesTest x y t / x := by
    unfold roughSaiasStieltjesTest
    field_simp [ht0, hx0]
  have hcongr := hquot.congr_of_eventuallyEq heq hvalue
  convert hcongr using 1
  simp only [id_eq]
  unfold roughSaiasStieltjesTest
    roughSaiasStieltjesTestRightDerivative
  field_simp [ht0, hx0, hlogy]
  ring

theorem continuousOn_roughSaiasRhoCoordinate
    {x y A B : ℝ} (_hy : 1 < y) (hA : 0 < A) :
    ContinuousOn
      (fun t : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y t))
      (Set.Icc A B) := by
  intro t ht
  have ht0 : t ≠ 0 := (hA.trans_le ht.1).ne'
  have hcoord : ContinuousAt (roughSaiasStieltjesCoordinate x y) t := by
    unfold roughSaiasStieltjesCoordinate
    exact (continuousAt_const.sub (Real.continuousAt_log ht0)).div_const _
  exact (continuous_rho.continuousAt.comp hcoord).continuousWithinAt

/-- The logarithmic-coordinate right derivative is integrable on the
compact natural interval. -/
theorem integrableOn_roughSaiasRhoCoordinateRightDerivative
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
          (-1 / (t * Real.log y)))
      (Set.Icc (1 : ℝ) (X : ℝ)) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hmeas : Measurable (fun t : ℝ ↦
      roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
        (-1 / (t * Real.log y))) :=
    (measurable_roughSaiasOpenFaceDickmanDerivative.comp
      (measurable_roughSaiasStieltjesCoordinate (X : ℝ) y)).mul
        (measurable_const.div (measurable_id.mul measurable_const))
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ 1 / Real.log y)
      volume (1 : ℝ) (X : ℝ) :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable (fun t : ℝ ↦
      roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
        (-1 / (t * Real.log y)))
      volume (1 : ℝ) (X : ℝ) := by
    apply hconst.mono_fun' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
      simpa only [Set.uIcc_of_le hXR] using Set.uIoc_subset_uIcc ht
    have htpos : 0 < t := zero_lt_one.trans_le htI.1
    have hcoord := roughSaiasStieltjesCoordinate_mem hy htI.1 htI.2
    have hD := roughSaiasOpenFaceDickmanDerivative_abs_le_one
      (hcoord.2.trans hu5)
    have hdenom : 0 < t * Real.log y := mul_pos htpos hlogy
    have hinv : 1 / (t * Real.log y) ≤ 1 / Real.log y := by
      apply one_div_le_one_div_of_le hlogy
      nlinarith [mul_le_mul_of_nonneg_right htI.1 hlogy.le]
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_one,
      abs_of_pos hdenom]
    calc
      |roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate (X : ℝ) y t)| *
          (1 / (t * Real.log y)) ≤
        1 * (1 / (t * Real.log y)) :=
          mul_le_mul_of_nonneg_right hD (by positivity)
      _ ≤ 1 * (1 / Real.log y) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 1 / Real.log y := one_mul _
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hXR).mp hint

/-- FTC for the Dickman coordinate, with the corner at coordinate `1`
handled by the right derivative rather than discarded. -/
theorem integral_roughSaiasRhoCoordinateRightDerivative
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    (∫ t in (1 : ℝ)..(X : ℝ),
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
          (-1 / (t * Real.log y))) =
      1 - rho (Real.log (X : ℝ) / Real.log y) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hcont := continuousOn_roughSaiasRhoCoordinate
    (x := (X : ℝ)) (y := y) (A := (1 : ℝ)) (B := (X : ℝ))
    hy (by norm_num)
  have hright : ∀ t ∈ Set.Ioo (1 : ℝ) (X : ℝ),
      HasDerivWithinAt
        (fun s : ℝ ↦ rho
          (roughSaiasStieltjesCoordinate (X : ℝ) y s))
        (roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
          (-1 / (t * Real.log y)))
        (Set.Ioi t) t := by
    intro t ht
    exact hasDerivWithinAt_roughSaiasRhoCoordinate_right hy ht.1.le
      ht.2.le hu5
  have hintIcc := integrableOn_roughSaiasRhoCoordinateRightDerivative
    hX hy hu5
  have hint : IntervalIntegrable
      (fun t : ℝ ↦
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
          (-1 / (t * Real.log y)))
      volume (1 : ℝ) (X : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hXR).mpr hintIcc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hXR hcont hright hint
  simpa [roughSaiasStieltjesCoordinate] using hftc

/-- Exact value of the smooth contribution to the floor correction. -/
theorem integral_roughSaiasStieltjesSmoothCorrection
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
        roughSaiasStieltjesSmoothCorrection X y t) =
      (X : ℝ) *
        (rho (Real.log (X : ℝ) / Real.log y) - 1) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  rw [← intervalIntegral.integral_of_le hXR]
  have heq :
      (∫ t in (1 : ℝ)..(X : ℝ),
          roughSaiasStieltjesSmoothCorrection X y t) =
        ∫ t in (1 : ℝ)..(X : ℝ),
          (-(X : ℝ)) *
            (roughSaiasOpenFaceDickmanDerivative
                (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
              (-1 / (t * Real.log y))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
      simpa [Set.uIcc_of_le hXR] using ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le htI.1).ne'
    unfold roughSaiasStieltjesSmoothCorrection
    field_simp [ht0, hlogy]
  rw [heq, intervalIntegral.integral_const_mul,
    integral_roughSaiasRhoCoordinateRightDerivative hX hy hu5]
  ring

theorem integrableOn_roughSaiasStieltjesSmoothCorrection
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    IntegrableOn (roughSaiasStieltjesSmoothCorrection X y)
      (Set.Ioc (1 : ℝ) (X : ℝ)) := by
  have hbase :=
    (integrableOn_roughSaiasRhoCoordinateRightDerivative hX hy hu5).mono_set
      Set.Ioc_subset_Icc_self
  have hmul := hbase.const_mul (-(X : ℝ))
  apply IntegrableOn.congr_fun_ae hmul
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htpos : 0 < t := zero_lt_one.trans ht.1
  have ht0 : t ≠ 0 := htpos.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  unfold roughSaiasStieltjesSmoothCorrection
  field_simp [ht0, hlogy]

/-! ## Identification of the signed fractional part -/

/-- The five-face hypothesis places the natural endpoint below the
artificial base-change cap `Y^5`. -/
theorem roughSaias_natCast_le_rpow_five
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    (X : ℝ) ≤ (Y : ℝ) ^ (5 : ℝ) := by
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hYpos : 0 < (Y : ℝ) := by positivity
  have hYone : 1 < (Y : ℝ) := by exact_mod_cast (show 1 < Y by omega)
  have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos hYone
  have hlogX : Real.log (X : ℝ) ≤
      5 * Real.log (Y : ℝ) := (div_le_iff₀ hlogY).mp hu5
  have hpowpos : 0 < (Y : ℝ) ^ (5 : ℝ) :=
    Real.rpow_pos_of_pos hYpos 5
  apply (Real.log_le_log_iff hXpos hpowpos).mp
  rw [Real.log_rpow hYpos]
  exact hlogX

/-- The base-free correction may be capped at `X` rather than `Y^5`, since
its Dickman derivative is already zero above `X/Y`. -/
theorem roughSaiasBaseFreeFractionalIntegral_eq_natCap
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral X Y =
      ∫ t in (1 : ℝ)..(X : ℝ),
        roughSaiasBaseFreeFractionalKernel X Y t := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hcap := roughSaias_natCast_le_rpow_five hX hY hu5
  have h1cap : (1 : ℝ) ≤ (Y : ℝ) ^ (5 : ℝ) :=
    hXR.trans hcap
  have hXmem : (X : ℝ) ∈
      Set.uIcc (1 : ℝ) ((Y : ℝ) ^ (5 : ℝ)) := by
    rw [Set.uIcc_of_le h1cap]
    exact ⟨hXR, hcap⟩
  have hint := roughSaiasBaseFreeFractionalKernel_intervalIntegrable
    (q := X) (m := Y) hY hu5
  have hparts := (IntervalIntegrable.trans_iff hXmem).mp hint
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hYone : 1 < (Y : ℝ) := by exact_mod_cast (show 1 < Y by omega)
  have hdivlt : (X : ℝ) / (Y : ℝ) < (X : ℝ) :=
    div_lt_self hXpos hYone
  have htail :
      (∫ t in (X : ℝ)..(Y : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel X Y t) = 0 := by
    calc
      _ = ∫ _t in (X : ℝ)..(Y : ℝ) ^ (5 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htI : t ∈
            Set.Icc (X : ℝ) ((Y : ℝ) ^ (5 : ℝ)) := by
          rw [Set.uIcc_of_le hcap] at ht
          exact ht
        exact roughSaiasBaseFreeFractionalKernel_eq_zero_of_div_lt
          hX hY (hdivlt.trans_le htI.1)
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hparts.1 hparts.2
  unfold roughSaiasBaseFreeFractionalIntegral
  rw [← hsplit, htail, add_zero]

/-- Away from the unique point `t=X/Y`, the open-face fractional
integrand is exactly `X` times the existing base-free kernel. -/
theorem roughSaiasStieltjesFractionalCorrection_eq_baseFree_of_ne
    {X Y : ℕ} {t : ℝ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (ht : 0 < t) (hne : t ≠ (X : ℝ) / (Y : ℝ)) :
    roughSaiasStieltjesFractionalCorrection X (Y : ℝ) t =
      (X : ℝ) * roughSaiasBaseFreeFractionalKernel X Y t := by
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hYpos : 0 < (Y : ℝ) := by positivity
  have hlogY : Real.log (Y : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < Y by omega)))
  have hcoordEq : roughSaiasStieltjesCoordinate (X : ℝ) (Y : ℝ) t =
      roughSaiasBaseFreeDickmanCoordinate X Y t := by
    rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
    rfl
  have hcoordNe :
      roughSaiasStieltjesCoordinate (X : ℝ) (Y : ℝ) t ≠ 1 := by
    intro hcoord
    have hlogEq : Real.log (X : ℝ) - Real.log t =
        Real.log (Y : ℝ) := by
      unfold roughSaiasStieltjesCoordinate at hcoord
      field_simp [hlogY] at hcoord
      linarith
    have hlogDiv : Real.log ((X : ℝ) / (Y : ℝ)) =
        Real.log (X : ℝ) - Real.log (Y : ℝ) := by
      rw [Real.log_div hXpos.ne' hYpos.ne']
    have hlogs : Real.log t =
        Real.log ((X : ℝ) / (Y : ℝ)) := by
      rw [hlogDiv]
      linarith
    have hexp := congrArg Real.exp hlogs
    rw [Real.exp_log ht,
      Real.exp_log (div_pos hXpos hYpos)] at hexp
    exact hne hexp
  unfold roughSaiasStieltjesFractionalCorrection
    roughSaiasBaseFreeFractionalKernel
  rw [hcoordEq,
    roughSaiasOpenFaceDickmanDerivative_eq_roughSaias
      (hcoordEq ▸ hcoordNe)]
  unfold roughSaiasBaseFreeDickmanCoordinate
  field_simp [ht.ne', hlogY]

theorem integrableOn_roughSaiasStieltjesFractionalCorrection
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    IntegrableOn (roughSaiasStieltjesFractionalCorrection X (Y : ℝ))
      (Set.Ioc (1 : ℝ) (X : ℝ)) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hcap := roughSaias_natCast_le_rpow_five hX hY hu5
  have hfull := roughSaiasBaseFreeFractionalKernel_intervalIntegrable
    (q := X) (m := Y) hY hu5
  have hcapInt : IntervalIntegrable
      (roughSaiasBaseFreeFractionalKernel X Y) volume
      (1 : ℝ) (X : ℝ) := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le hXR,
      Set.uIcc_of_le (hXR.trans hcap)]
    exact Set.Icc_subset_Icc le_rfl hcap
  have hbaseIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hXR).mp hcapInt
  have hbaseIccMul : IntegrableOn
      (fun t : ℝ => (X : ℝ) * roughSaiasBaseFreeFractionalKernel X Y t)
      (Set.Icc (1 : ℝ) (X : ℝ)) :=
    hbaseIcc.const_mul (X : ℝ)
  have hbase := hbaseIccMul.mono_set Set.Ioc_subset_Icc_self
  apply IntegrableOn.congr_fun_ae hbase
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [((volume : Measure ℝ).ae_ne
    ((X : ℝ) / (Y : ℝ)))] with t hne ht
  exact (roughSaiasStieltjesFractionalCorrection_eq_baseFree_of_ne
    hX hY (zero_lt_one.trans ht.1) hne).symm

/-- Exact value of the fractional contribution. -/
theorem integral_roughSaiasStieltjesFractionalCorrection
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
        roughSaiasStieltjesFractionalCorrection X (Y : ℝ) t) =
      (X : ℝ) * roughSaiasBaseFreeFractionalIntegral X Y := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  rw [← intervalIntegral.integral_of_le hXR]
  have heq :
      (∫ t in (1 : ℝ)..(X : ℝ),
          roughSaiasStieltjesFractionalCorrection X (Y : ℝ) t) =
        ∫ t in (1 : ℝ)..(X : ℝ),
          (X : ℝ) * roughSaiasBaseFreeFractionalKernel X Y t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [((volume : Measure ℝ).ae_ne
      ((X : ℝ) / (Y : ℝ)))] with t hne ht
    have htI : t ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
      simpa only [Set.uIcc_of_le hXR] using Set.uIoc_subset_uIcc ht
    exact roughSaiasStieltjesFractionalCorrection_eq_baseFree_of_ne
      hX hY (zero_lt_one.trans_le htI.1) hne
  rw [heq, intervalIntegral.integral_const_mul,
    ← roughSaiasBaseFreeFractionalIntegral_eq_natCap hX hY hu5]

/-! ## Final natural-endpoint identification -/

/-- The compact atom-minus-density definition and the existing finite
Saias normal form are exactly equal at every positive natural endpoint on
the five constructed faces. -/
theorem roughSaiasLambdaStieltjesWithCutoff_nat_eq_normalForm
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) (Y : ℝ) =
      roughSaiasLambdaNormalForm (X : ℝ) Y := by
  have hsmooth := integrableOn_roughSaiasStieltjesSmoothCorrection
    hX (by exact_mod_cast (show 1 < Y by omega)) hu5
  have hfract := integrableOn_roughSaiasStieltjesFractionalCorrection
    hX hY hu5
  have hsplit := MeasureTheory.integral_sub hsmooth hfract
  rw [roughSaiasLambdaStieltjesWithCutoff_nat_eq_add_floorCorrection
      hX (by exact_mod_cast (show 1 < Y by omega)) hu5]
  have hpoint :
      (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          roughSaiasStieltjesFloorCorrection X (Y : ℝ) t) =
        ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          (roughSaiasStieltjesSmoothCorrection X (Y : ℝ) t -
            roughSaiasStieltjesFractionalCorrection X (Y : ℝ) t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact roughSaiasStieltjesFloorCorrection_eq_smooth_sub_fractional
      (zero_lt_one.trans ht.1)
      (by exact_mod_cast (show 1 < Y by omega))
  rw [hpoint, hsplit,
    integral_roughSaiasStieltjesSmoothCorrection hX
      (by exact_mod_cast (show 1 < Y by omega)) hu5,
    integral_roughSaiasStieltjesFractionalCorrection hX hY hu5]
  rw [← roughSaiasNaturalMain_eq_lambdaNormalForm,
    roughSaiasNaturalMain_eq_rho_sub_baseFree hY]
  ring

/-- Canonical-cap version of the same natural-endpoint identity. -/
theorem roughSaiasLambdaStieltjes_nat_eq_normalForm
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    roughSaiasLambdaStieltjes (X : ℝ) (Y : ℝ) =
      roughSaiasLambdaNormalForm (X : ℝ) Y := by
  rw [roughSaiasLambdaStieltjes_nat]
  exact roughSaiasLambdaStieltjesWithCutoff_nat_eq_normalForm hX hY hu5

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasRealStieltjesNormalForm -/
section


/-!
# Real-endpoint identification of the Stieltjes and Saias normal forms

The natural-endpoint calculation in `RoughSaiasStieltjesNormalForm` is
extended here to every real outer endpoint `x ≥ 1`.  Abel summation now
produces `floor x`, and the elementary identity

`floor x = x - fract x`

supplies exactly the terminal sawtooth in `roughSaiasLambdaNormalForm`.
This real version is needed in continuous Buchstab at the inner endpoints
`x/s`.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Real floor-correction kernels -/







theorem roughSaiasRealStieltjesFloorCorrection_eq_smooth_sub_fractional
    {x y t : ℝ} (ht : 0 < t) (hy : 1 < y) :
    roughSaiasRealStieltjesFloorCorrection x y t =
      roughSaiasRealStieltjesSmoothCorrection x y t -
        roughSaiasRealStieltjesFractionalCorrection x y t := by
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have ht0 : t ≠ 0 := ht.ne'
  unfold roughSaiasRealStieltjesFloorCorrection
    roughSaiasRealStieltjesSmoothCorrection
    roughSaiasRealStieltjesFractionalCorrection
  rw [roughSaiasNatFloor_cast_eq_sub_fract ht.le]
  field_simp [ht0, hlogy]

theorem roughSaiasRealStieltjesDerivativeFloor_add_density
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (htx : t ≤ x) :
    roughSaiasStieltjesTestRightDerivative x y t *
          (((⌊t⌋₊ : ℕ) : ℝ)) +
        roughSaiasStieltjesDickmanProfile x y t *
          roughSaiasFloorDensity t =
      -roughSaiasRealStieltjesFloorCorrection x y t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  rw [roughSaiasStieltjesDickmanProfile_eq_mul_test hx hy ht htx]
  unfold roughSaiasStieltjesTestRightDerivative
    roughSaiasStieltjesTest roughSaiasFloorDensity
    roughSaiasRealStieltjesFloorCorrection
  field_simp [ht0, hlogy]
  ring

/-! ## Real compact integrability -/

theorem integrableOn_roughSaiasRealStieltjesTestRightDerivative
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn (roughSaiasStieltjesTestRightDerivative x y)
      (Set.Icc (1 : ℝ) x) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hC : 0 ≤ x * (1 / Real.log y + 1) := by
    have hlogy : 0 < Real.log y := Real.log_pos hy
    positivity
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ x * (1 / Real.log y + 1))
      volume (1 : ℝ) x :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable
      (roughSaiasStieltjesTestRightDerivative x y)
      volume (1 : ℝ) x := by
    apply hconst.mono_fun'
      (measurable_roughSaiasStieltjesTestRightDerivative x y).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    rw [Real.norm_eq_abs]
    exact roughSaiasStieltjesTestRightDerivative_abs_le
      hy htI.1 htI.2 hu5
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hint

theorem integrableOn_roughSaiasRealStieltjesDerivative_mul_floor
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦ roughSaiasStieltjesTestRightDerivative x y t *
        (((⌊t⌋₊ : ℕ) : ℝ)))
      (Set.Ioc (1 : ℝ) x) := by
  have hint := integrableOn_roughSaiasRealStieltjesTestRightDerivative
    hx1 hy hu5
  have hmul := integrableOn_mul_sum_Icc
    FriableAsymptotic.positiveIncrement (a := (1 : ℝ))
      (b := x) (m := 0) (by norm_num) hint
  have hmul' := hmul.mono_set Set.Ioc_subset_Icc_self
  simpa only [roughSaiasPositiveIncrement_prefix] using hmul'

theorem integrableOn_roughSaiasRealStieltjesProfile_mul_floorDensity
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦ roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) x) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hx0 : 0 ≤ x := hx.le
  have hmeas : Measurable (fun t : ℝ ↦
      roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t) :=
    (measurable_roughSaiasStieltjesDickmanProfile x y).mul
      measurable_roughSaiasFloorDensity
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ x)
      volume (1 : ℝ) x :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable (fun t : ℝ ↦
      roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t) volume (1 : ℝ) x := by
    apply hconst.mono_fun' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    have htpos : 0 < t := zero_lt_one.trans_le htI.1
    have hcoord := roughSaiasStieltjesCoordinate_mem hy htI.1 htI.2
    have hcoordLog5 : Real.log (x / t) / Real.log y ≤ 5 := by
      rw [← roughSaiasStieltjesCoordinate_eq_log_div hx htpos]
      exact hcoord.2.trans hu5
    have hrho := roughSaiasZeroExtendedRho_mem_unitInterval hcoordLog5
    have hprofile0 : 0 ≤ roughSaiasStieltjesDickmanProfile x y t := by
      unfold roughSaiasStieltjesDickmanProfile
      exact mul_nonneg hx0 hrho.1
    have hprofilex : roughSaiasStieltjesDickmanProfile x y t ≤ x := by
      unfold roughSaiasStieltjesDickmanProfile
      exact (mul_le_mul_of_nonneg_left hrho.2 hx0).trans_eq (mul_one _)
    have hfloor0 : (0 : ℝ) ≤ (((⌊t⌋₊ : ℕ) : ℝ)) := by positivity
    have hfloort : (((⌊t⌋₊ : ℕ) : ℝ)) ≤ t := Nat.floor_le htpos.le
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
    have hdensity0 : 0 ≤ roughSaiasFloorDensity t := by
      unfold roughSaiasFloorDensity
      exact div_nonneg hfloor0 ht2.le
    have hdensity1 : roughSaiasFloorDensity t ≤ 1 := by
      unfold roughSaiasFloorDensity
      apply (div_le_one ht2).2
      have hquad : 0 ≤ t * (t - 1) :=
        mul_nonneg htpos.le (sub_nonneg.mpr htI.1)
      exact hfloort.trans (by nlinarith)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hprofile0 hdensity0)]
    calc
      roughSaiasStieltjesDickmanProfile x y t * roughSaiasFloorDensity t ≤
          roughSaiasStieltjesDickmanProfile x y t * 1 :=
        mul_le_mul_of_nonneg_left hdensity1 hprofile0
      _ ≤ x * 1 := mul_le_mul_of_nonneg_right hprofilex (by norm_num)
      _ = x := mul_one _
  have hintIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hint
  exact hintIcc.mono_set Set.Ioc_subset_Icc_self

/-! ## Abel summation at a real endpoint -/

theorem roughSaiasStieltjesAtomPart_ceil_profile_eq_floor_test
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y) :
    roughSaiasStieltjesAtomPart ⌈x⌉₊
        (roughSaiasStieltjesDickmanProfile x y) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        roughSaiasStieltjesTest x y (n : ℝ) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hfloorceil : ⌊x⌋₊ ≤ ⌈x⌉₊ := by
    have h := Nat.floor_le_floor (Nat.le_ceil x)
    simpa using h
  have hsubset : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.Icc 1 ⌈x⌉₊ := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hfloorceil⟩
  have hsum :
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          roughSaiasStieltjesDickmanProfile x y (n : ℝ) / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 ⌈x⌉₊,
          roughSaiasStieltjesDickmanProfile x y (n : ℝ) / (n : ℝ) := by
    apply Finset.sum_subset hsubset
    intro n hnceil hnfloor
    have hnData := Finset.mem_Icc.mp hnceil
    have hfloorlt : ⌊x⌋₊ < n := by
      by_contra hnot
      exact hnfloor (Finset.mem_Icc.mpr
        ⟨hnData.1, le_of_not_gt hnot⟩)
    have hxt : x < (n : ℝ) :=
      (Nat.floor_lt' (by omega)).mp hfloorlt
    rw [roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
      hx hy (by exact_mod_cast (show 0 < n by omega)) hxt, zero_div]
  unfold roughSaiasStieltjesAtomPart
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnData := Finset.mem_Icc.mp hn
  have hnx : (n : ℝ) ≤ x :=
    (by exact_mod_cast hnData.2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
      (Nat.floor_le hx.le)
  exact roughSaiasStieltjesDickmanProfile_div_eq_test
    hx hy (by exact_mod_cast (show 0 < n by omega)) hnx

theorem roughSaiasStieltjesTest_floor_sum_eq_endpoint_sub_integral
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        roughSaiasStieltjesTest x y (n : ℝ)) =
      (⌊x⌋₊ : ℝ) -
        ∫ t in Set.Ioc (1 : ℝ) x,
          roughSaiasStieltjesTestRightDerivative x y t *
            (((⌊t⌋₊ : ℕ) : ℝ)) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hcont := continuousOn_roughSaiasStieltjesTest
    (x := x) (y := y) (A := (1 : ℝ)) (B := x) hy (by norm_num)
  have hright := roughSaiasStieltjesTest_hasRightDerivOn
    (x := x) (y := y) (R := x) hy hx1 le_rfl hu5
  have hint := integrableOn_roughSaiasRealStieltjesTestRightDerivative
    hx1 hy hu5
  have hAbel :=
    RoughSaiasRightAbel.sum_mul_eq_sub_sub_integral_mul_right
      FriableAsymptotic.positiveIncrement
      (a := (1 : ℝ)) (b := x) (by norm_num) hx1
      hcont hright hint
  have hweighted :
      (∑ k ∈ Finset.Ioc 1 ⌊x⌋₊,
          roughSaiasStieltjesTest x y (k : ℝ) *
            FriableAsymptotic.positiveIncrement k) =
        ∑ k ∈ Finset.Ioc 1 ⌊x⌋₊,
          roughSaiasStieltjesTest x y (k : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      rw [Finset.mem_Ioc] at hk
      omega
    simp [FriableAsymptotic.positiveIncrement, hk0]
  have hfloor1 : 1 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using hx1
  simp only [Nat.floor_one] at hAbel
  rw [hweighted] at hAbel
  simp_rw [roughSaiasPositiveIncrement_prefix] at hAbel
  rw [roughSaiasStieltjesTest_self hx.ne'] at hAbel
  nth_rewrite 1 [Finset.Icc_eq_cons_Ioc hfloor1]
  rw [Finset.sum_cons, hAbel]
  ring

theorem roughSaiasStieltjesDensityPart_ceil_profile_eq_realCap
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y) :
    roughSaiasStieltjesDensityPart ⌈x⌉₊
        (roughSaiasStieltjesDickmanProfile x y) =
      ∫ t in Set.Ioc (1 : ℝ) x,
        roughSaiasStieltjesDickmanProfile x y t *
          roughSaiasFloorDensity t := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hsubset : Set.Ioc (1 : ℝ) x ⊆
      Set.Ioc (1 : ℝ) (⌈x⌉₊ : ℝ) := by
    rintro t ⟨ht1, htx⟩
    exact ⟨ht1, htx.trans (Nat.le_ceil x)⟩
  unfold roughSaiasStieltjesDensityPart
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
    measurableSet_Ioc hsubset
  intro t ht
  have hxt : x < t := by
    by_contra hnot
    exact ht.2 ⟨ht.1.1, le_of_not_gt hnot⟩
  rw [roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
    hx hy (zero_lt_one.trans ht.1.1) hxt, zero_mul]

theorem roughSaiasLambdaStieltjes_eq_floor_add_floorCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    roughSaiasLambdaStieltjes x y =
      (⌊x⌋₊ : ℝ) +
        ∫ t in Set.Ioc (1 : ℝ) x,
          roughSaiasRealStieltjesFloorCorrection x y t := by
  have hderiv := integrableOn_roughSaiasRealStieltjesDerivative_mul_floor
    hx1 hy hu5
  have hdensity :=
    integrableOn_roughSaiasRealStieltjesProfile_mul_floorDensity
      hx1 hy hu5
  unfold roughSaiasLambdaStieltjes roughSaiasLambdaStieltjesWithCutoff
    roughSaiasFiniteStieltjesFunctional
  rw [roughSaiasStieltjesAtomPart_ceil_profile_eq_floor_test hx1 hy,
    roughSaiasStieltjesTest_floor_sum_eq_endpoint_sub_integral hx1 hy hu5,
    roughSaiasStieltjesDensityPart_ceil_profile_eq_realCap hx1 hy]
  have hadd := MeasureTheory.integral_add hderiv hdensity
  have hpoint :
      (∫ t in Set.Ioc (1 : ℝ) x,
          (roughSaiasStieltjesTestRightDerivative x y t *
              (((⌊t⌋₊ : ℕ) : ℝ)) +
            roughSaiasStieltjesDickmanProfile x y t *
              roughSaiasFloorDensity t)) =
        ∫ t in Set.Ioc (1 : ℝ) x,
          -roughSaiasRealStieltjesFloorCorrection x y t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact roughSaiasRealStieltjesDerivativeFloor_add_density
      (zero_lt_one.trans_le hx1) hy (zero_lt_one.trans ht.1) ht.2
  calc
    (⌊x⌋₊ : ℝ) -
          (∫ t in Set.Ioc (1 : ℝ) x,
            roughSaiasStieltjesTestRightDerivative x y t *
              (((⌊t⌋₊ : ℕ) : ℝ))) -
          (∫ t in Set.Ioc (1 : ℝ) x,
            roughSaiasStieltjesDickmanProfile x y t *
              roughSaiasFloorDensity t) =
        (⌊x⌋₊ : ℝ) -
          ((∫ t in Set.Ioc (1 : ℝ) x,
              roughSaiasStieltjesTestRightDerivative x y t *
                (((⌊t⌋₊ : ℕ) : ℝ))) +
            (∫ t in Set.Ioc (1 : ℝ) x,
              roughSaiasStieltjesDickmanProfile x y t *
                roughSaiasFloorDensity t)) := by ring
    _ = (⌊x⌋₊ : ℝ) -
          ∫ t in Set.Ioc (1 : ℝ) x,
            (roughSaiasStieltjesTestRightDerivative x y t *
                (((⌊t⌋₊ : ℕ) : ℝ)) +
              roughSaiasStieltjesDickmanProfile x y t *
                roughSaiasFloorDensity t) := by rw [hadd]
    _ = (⌊x⌋₊ : ℝ) -
          ∫ t in Set.Ioc (1 : ℝ) x,
            -roughSaiasRealStieltjesFloorCorrection x y t := by rw [hpoint]
    _ = (⌊x⌋₊ : ℝ) +
          ∫ t in Set.Ioc (1 : ℝ) x,
            roughSaiasRealStieltjesFloorCorrection x y t := by
      rw [MeasureTheory.integral_neg]
      ring

/-! ## Smooth real contribution -/

theorem integrableOn_roughSaiasRealRhoCoordinateRightDerivative
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)))
      (Set.Icc (1 : ℝ) x) := by
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hmeas : Measurable (fun t : ℝ ↦
      roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t) *
        (-1 / (t * Real.log y))) :=
    (measurable_roughSaiasOpenFaceDickmanDerivative.comp
      (measurable_roughSaiasStieltjesCoordinate x y)).mul
        (measurable_const.div (measurable_id.mul measurable_const))
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ 1 / Real.log y) volume (1 : ℝ) x :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable (fun t : ℝ ↦
      roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t) *
        (-1 / (t * Real.log y))) volume (1 : ℝ) x := by
    apply hconst.mono_fun' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    have htpos : 0 < t := zero_lt_one.trans_le htI.1
    have hcoord := roughSaiasStieltjesCoordinate_mem hy htI.1 htI.2
    have hD := roughSaiasOpenFaceDickmanDerivative_abs_le_one
      (hcoord.2.trans hu5)
    have hdenom : 0 < t * Real.log y := mul_pos htpos hlogy
    have hinv : 1 / (t * Real.log y) ≤ 1 / Real.log y := by
      apply one_div_le_one_div_of_le hlogy
      nlinarith [mul_le_mul_of_nonneg_right htI.1 hlogy.le]
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_one,
      abs_of_pos hdenom]
    calc
      |roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t)| *
          (1 / (t * Real.log y)) ≤
        1 * (1 / (t * Real.log y)) :=
          mul_le_mul_of_nonneg_right hD (by positivity)
      _ ≤ 1 * (1 / Real.log y) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 1 / Real.log y := one_mul _
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hint

theorem integral_roughSaiasRealRhoCoordinateRightDerivative
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∫ t in (1 : ℝ)..x,
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y))) =
      1 - rho (Real.log x / Real.log y) := by
  have hcont := continuousOn_roughSaiasRhoCoordinate
    (x := x) (y := y) (A := (1 : ℝ)) (B := x) hy (by norm_num)
  have hright : ∀ t ∈ Set.Ioo (1 : ℝ) x,
      HasDerivWithinAt
        (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
        (roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)))
        (Set.Ioi t) t := by
    intro t ht
    exact hasDerivWithinAt_roughSaiasRhoCoordinate_right
      hy ht.1.le ht.2.le hu5
  have hintIcc := integrableOn_roughSaiasRealRhoCoordinateRightDerivative
    hx1 hy hu5
  have hint : IntervalIntegrable
      (fun t : ℝ ↦
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)))
      volume (1 : ℝ) x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mpr hintIcc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hx1 hcont hright hint
  simpa [roughSaiasStieltjesCoordinate] using hftc

theorem integral_roughSaiasRealStieltjesSmoothCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) x,
        roughSaiasRealStieltjesSmoothCorrection x y t) =
      x * (rho (Real.log x / Real.log y) - 1) := by
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  rw [← intervalIntegral.integral_of_le hx1]
  have heq :
      (∫ t in (1 : ℝ)..x,
          roughSaiasRealStieltjesSmoothCorrection x y t) =
        ∫ t in (1 : ℝ)..x,
          (-x) *
            (roughSaiasOpenFaceDickmanDerivative
                (roughSaiasStieltjesCoordinate x y t) *
              (-1 / (t * Real.log y))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa [Set.uIcc_of_le hx1] using ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le htI.1).ne'
    unfold roughSaiasRealStieltjesSmoothCorrection
    field_simp [ht0, hlogy]
  rw [heq, intervalIntegral.integral_const_mul,
    integral_roughSaiasRealRhoCoordinateRightDerivative hx1 hy hu5]
  ring

theorem integrableOn_roughSaiasRealStieltjesSmoothCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn (roughSaiasRealStieltjesSmoothCorrection x y)
      (Set.Ioc (1 : ℝ) x) := by
  have hbase :=
    (integrableOn_roughSaiasRealRhoCoordinateRightDerivative
      hx1 hy hu5).mono_set Set.Ioc_subset_Icc_self
  have hmul := hbase.const_mul (-x)
  apply IntegrableOn.congr_fun_ae hmul
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht.1).ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  unfold roughSaiasRealStieltjesSmoothCorrection
  field_simp [ht0, hlogy]

/-! ## Fractional real contribution -/







/-! ## Exact real-endpoint identification -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFullyRealNormalForm -/
section


/-!
# The Saias normal form with a genuinely real base

Continuous Buchstab produces inner terms `Lambda(x/s,s)` with a real base
`s`.  The project's original `roughSaiasG` takes a natural base, so it
cannot state that identity directly.  This file supplies the literal real
analogue, proves the same signed base-free substitution, and identifies it
exactly with the finite Stieltjes functional.  At natural bases it reduces
definitionally to the existing normal form.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Fully real Saias data -/











theorem measurable_roughSaiasFullyRealFractionalWeight
    {y : ℝ} (hy : 0 < y) :
    Measurable (roughSaiasFullyRealFractionalWeight y) := by
  have hpow : Continuous (fun v : ℝ ↦ y ^ v) :=
    Real.continuous_const_rpow hy.ne'
  have hpowNeg : Continuous (fun v : ℝ ↦ y ^ (-v)) :=
    hpow.comp continuous_neg
  exact hpow.measurable.fract.mul hpowNeg.measurable

theorem roughSaiasFullyRealFractionalWeight_mem_unitInterval
    {y v : ℝ} (hy : 1 ≤ y) (hv : 0 ≤ v) :
    0 ≤ roughSaiasFullyRealFractionalWeight y v ∧
      roughSaiasFullyRealFractionalWeight y v ≤ 1 := by
  have hpowNonneg : 0 ≤ y ^ (-v) := Real.rpow_nonneg (by positivity) _
  have hpowLe : y ^ (-v) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
  have hfractNonneg : 0 ≤ Int.fract (y ^ v) := Int.fract_nonneg _
  have hfractLe : Int.fract (y ^ v) ≤ 1 := (Int.fract_lt_one _).le
  unfold roughSaiasFullyRealFractionalWeight
  constructor
  · exact mul_nonneg hfractNonneg hpowNonneg
  · calc
      Int.fract (y ^ v) * y ^ (-v) ≤ 1 * y ^ (-v) :=
        mul_le_mul_of_nonneg_right hfractLe hpowNonneg
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hpowLe (by norm_num)
      _ = 1 := mul_one _

theorem roughSaiasFullyRealIntegrand_intervalIntegrable
    {y u : ℝ} (hy : 1 < y) (hu5 : u ≤ 5) :
    IntervalIntegrable
      (fun v : ℝ ↦ roughSaiasDickmanDerivative (u - v) *
        roughSaiasFullyRealFractionalWeight y v)
      volume 0 5 := by
  have hmeas : Measurable
      (fun v : ℝ ↦ roughSaiasDickmanDerivative (u - v) *
        roughSaiasFullyRealFractionalWeight y v) :=
    (measurable_roughSaiasDickmanDerivative.comp
      (measurable_const.sub measurable_id)).mul
        (measurable_roughSaiasFullyRealFractionalWeight
          (zero_lt_one.trans hy))
  have hone : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume 0 5 :=
    continuous_const.intervalIntegrable 0 5
  apply hone.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  have hv' : v ∈ Set.Icc (0 : ℝ) 5 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using
      Set.uIoc_subset_uIcc hv
  have hderiv := roughSaiasDickmanDerivative_abs_le_one
    (u := u - v) (by linarith [hv'.1])
  have hweight := roughSaiasFullyRealFractionalWeight_mem_unitInterval
    hy.le hv'.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight.1]
  calc
    |roughSaiasDickmanDerivative (u - v)| *
        roughSaiasFullyRealFractionalWeight y v ≤
      1 * roughSaiasFullyRealFractionalWeight y v :=
        mul_le_mul_of_nonneg_right hderiv hweight.1
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hweight.2 (by norm_num)
    _ = 1 := mul_one _

/-! ## Exact real-base substitution -/

theorem roughSaiasFullyRealBaseFreeKernel_rpow_mul_jacobian
    {x y : ℝ} (hy : 1 < y) (v : ℝ) :
    (Real.log y * y ^ v) *
        roughSaiasFullyRealBaseFreeFractionalKernel x y (y ^ v) =
      roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
        roughSaiasFullyRealFractionalWeight y v := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have hrpow : y ^ v ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hypos v)
  have hcancel : v * Real.log y / Real.log y = v := by
    field_simp [hlogy]
  have hcoord :
      (Real.log x - v * Real.log y) / Real.log y =
        Real.log x / Real.log y - v := by
    rw [sub_div, hcancel]
  unfold roughSaiasFullyRealBaseFreeFractionalKernel
    roughSaiasFullyRealFractionalWeight
  rw [Real.log_rpow hypos, hcoord, Real.rpow_neg hypos.le]
  field_simp [hlogy, hrpow]

theorem roughSaiasFullyRealFractionalIntegral_eq_baseFree
    {x y : ℝ} (hy : 1 < y) :
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v) =
      roughSaiasFullyRealBaseFreeFractionalIntegral x y := by
  let f : ℝ → ℝ := fun v ↦ y ^ v
  let f' : ℝ → ℝ := fun v ↦ Real.log y * y ^ v
  have hypos : 0 < y := zero_lt_one.trans hy
  have hfderiv : ∀ v ∈ Set.Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Set.Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hypos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hy).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hypos.ne').continuousOn
  have hfimage : f '' Set.Icc (0 : ℝ) 5 =
      Set.Icc (1 : ℝ) (y ^ (5 : ℝ)) := by
    calc
      f '' Set.Icc (0 : ℝ) 5 = Set.Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Set.Icc (1 : ℝ) (y ^ (5 : ℝ)) := by simp [f]
  have hchange :
      (∫ t in f '' Set.Icc (0 : ℝ) 5,
          roughSaiasFullyRealBaseFreeFractionalKernel x y t) =
        ∫ v in Set.Icc (0 : ℝ) 5,
          f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v) :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasFullyRealBaseFreeFractionalKernel x y)
  have hpoint (v : ℝ) :
      f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v) =
        roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v := by
    simpa [f, f', smul_eq_mul] using
      roughSaiasFullyRealBaseFreeKernel_rpow_mul_jacobian
        (x := x) hy v
  have hu : (1 : ℝ) ≤ y ^ (5 : ℝ) :=
    Real.one_le_rpow hy.le (by norm_num)
  unfold roughSaiasFullyRealBaseFreeFractionalIntegral
  calc
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v) =
        ∫ v in Set.Icc (0 : ℝ) 5,
          roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
            roughSaiasFullyRealFractionalWeight y v := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ v in Set.Icc (0 : ℝ) 5,
          f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v _hv
      exact (hpoint v).symm
    _ = ∫ t in Set.Icc (1 : ℝ) (y ^ (5 : ℝ)),
          roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
      rw [← hfimage]
      exact hchange.symm
    _ = ∫ t in (1 : ℝ)..y ^ (5 : ℝ),
          roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
      rw [intervalIntegral.integral_of_le hu,
        MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
    {x y : ℝ} (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntervalIntegrable
      (roughSaiasFullyRealBaseFreeFractionalKernel x y)
      volume (1 : ℝ) (y ^ (5 : ℝ)) := by
  let f : ℝ → ℝ := fun v ↦ y ^ v
  let f' : ℝ → ℝ := fun v ↦ Real.log y * y ^ v
  have hypos : 0 < y := zero_lt_one.trans hy
  have hfderiv : ∀ v ∈ Set.Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Set.Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hypos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hy).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hypos.ne').continuousOn
  have hfimage : f '' Set.Icc (0 : ℝ) 5 =
      Set.Icc (1 : ℝ) (y ^ (5 : ℝ)) := by
    calc
      f '' Set.Icc (0 : ℝ) 5 = Set.Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Set.Icc (1 : ℝ) (y ^ (5 : ℝ)) := by simp [f]
  have horiginal : IntervalIntegrable
      (fun v : ℝ ↦
        roughSaiasDickmanDerivative
            (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v)
      volume 0 5 :=
    roughSaiasFullyRealIntegrand_intervalIntegrable hy hu5
  have horiginalIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0 : ℝ) ≤ 5)).mp horiginal
  have hjacobianIcc : IntegrableOn
      (fun v : ℝ ↦
        f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v))
      (Set.Icc (0 : ℝ) 5) := by
    apply horiginalIcc.congr_fun _ measurableSet_Icc
    intro v _hv
    simpa [f, f', smul_eq_mul] using
      (roughSaiasFullyRealBaseFreeKernel_rpow_mul_jacobian
        (x := x) hy v).symm
  have hkernelImage : IntegrableOn
      (roughSaiasFullyRealBaseFreeFractionalKernel x y)
      (f '' Set.Icc (0 : ℝ) 5) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasFullyRealBaseFreeFractionalKernel x y)).mpr hjacobianIcc
  rw [hfimage] at hkernelImage
  have hu : (1 : ℝ) ≤ y ^ (5 : ℝ) :=
    Real.one_le_rpow hy.le (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hu).mpr hkernelImage

theorem roughSaiasFullyRealBaseFreeKernel_eq_zero_of_div_lt
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : x / y < t) :
    roughSaiasFullyRealBaseFreeFractionalKernel x y t = 0 := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have htpos : 0 < t := (div_pos hx hypos).trans ht
  have hx_lt_ty : x < t * y := (div_lt_iff₀ hypos).mp ht
  have hloglt : Real.log x < Real.log t + Real.log y := by
    have h := Real.strictMonoOn_log hx (mul_pos htpos hypos) hx_lt_ty
    rwa [Real.log_mul htpos.ne' hypos.ne'] at h
  have harg : (Real.log x - Real.log t) / Real.log y < 1 := by
    rw [div_lt_one (Real.log_pos hy)]
    linarith
  unfold roughSaiasFullyRealBaseFreeFractionalKernel
  rw [roughSaiasDickmanDerivative_of_lt_one harg]
  simp

theorem roughSaiasFullyReal_le_rpow_five
    {x y : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    x ≤ y ^ (5 : ℝ) := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogx : Real.log x ≤ 5 * Real.log y :=
    (div_le_iff₀ hlogy).mp hu5
  have hcappos : 0 < y ^ (5 : ℝ) := Real.rpow_pos_of_pos hypos 5
  apply (Real.log_le_log_iff hx hcappos).mp
  rw [Real.log_rpow hypos]
  exact hlogx

theorem roughSaiasFullyRealBaseFreeIntegral_eq_realCap
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    roughSaiasFullyRealBaseFreeFractionalIntegral x y =
      ∫ t in (1 : ℝ)..x,
        roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hcap := roughSaiasFullyReal_le_rpow_five hx hy hu5
  have hxmem : x ∈ Set.uIcc (1 : ℝ) (y ^ (5 : ℝ)) := by
    rw [Set.uIcc_of_le (hx1.trans hcap)]
    exact ⟨hx1, hcap⟩
  have hint := roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
    (x := x) hy hu5
  have hparts := (IntervalIntegrable.trans_iff hxmem).mp hint
  have hdivlt : x / y < x := div_lt_self hx hy
  have htail :
      (∫ t in x..y ^ (5 : ℝ),
          roughSaiasFullyRealBaseFreeFractionalKernel x y t) = 0 := by
    calc
      _ = ∫ _t in x..y ^ (5 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htI : t ∈ Set.Icc x (y ^ (5 : ℝ)) := by
          rw [Set.uIcc_of_le hcap] at ht
          exact ht
        exact roughSaiasFullyRealBaseFreeKernel_eq_zero_of_div_lt
          hx hy (hdivlt.trans_le htI.1)
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hparts.1 hparts.2
  unfold roughSaiasFullyRealBaseFreeFractionalIntegral
  rw [← hsplit, htail, add_zero]

theorem roughSaiasFullyRealG_eq_rho_sub_baseFree
    {x y : ℝ} (hy : 1 < y) :
    roughSaiasFullyRealG y (Real.log x / Real.log y) =
      rho (Real.log x / Real.log y) -
        roughSaiasFullyRealBaseFreeFractionalIntegral x y := by
  unfold roughSaiasFullyRealG
  rw [roughSaiasFullyRealFractionalIntegral_eq_baseFree hy]

/-- The fully real normalizer is exactly one on its initial Dickman face. -/
theorem roughSaiasFullyRealG_eq_one_of_le_one
    {y u : ℝ} (hu : u ≤ 1) :
    roughSaiasFullyRealG y u = 1 := by
  have hzero :
      (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative (u - v) *
          roughSaiasFullyRealFractionalWeight y v) = 0 := by
    have hcongr :
        (∫ v in (0 : ℝ)..5,
          roughSaiasDickmanDerivative (u - v) *
            roughSaiasFullyRealFractionalWeight y v) =
          ∫ _v in (0 : ℝ)..5, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ∈ Set.Icc (0 : ℝ) 5 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using hv
      by_cases huv : u - v < 1
      · simp [roughSaiasDickmanDerivative_of_lt_one huv]
      · have huEq : u = 1 := by linarith [hv'.1]
        have hvEq : v = 0 := by linarith [hv'.1]
        subst u
        subst v
        simp [roughSaiasFullyRealFractionalWeight]
    simpa using hcongr
  rw [roughSaiasFullyRealG, hzero, sub_zero, rho_eq_one_of_le_one hu]

/-- The compact `3`-Lipschitz estimate is independent of whether the base
is natural: its proof uses only that the fractional weight lies in `[0,1]`.
-/
theorem roughSaiasFullyRealG_lipschitz_three
    {y : ℝ} (hy : 1 < y) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 5) (hb : b ∈ Set.Icc (0 : ℝ) 5) :
    |roughSaiasFullyRealG y a - roughSaiasFullyRealG y b| ≤
      3 * |a - b| := by
  let Fa : ℝ → ℝ := fun v ↦
    roughSaiasDickmanDerivative (a - v) *
      roughSaiasFullyRealFractionalWeight y v
  let Fb : ℝ → ℝ := fun v ↦
    roughSaiasDickmanDerivative (b - v) *
      roughSaiasFullyRealFractionalWeight y v
  let qa : ℝ → ℝ := fun v ↦ roughSaiasDickmanDerivative (a - v)
  let qb : ℝ → ℝ := fun v ↦ roughSaiasDickmanDerivative (b - v)
  have hFa : IntervalIntegrable Fa volume 0 5 := by
    simpa only [Fa] using
      roughSaiasFullyRealIntegrand_intervalIntegrable hy ha.2
  have hFb : IntervalIntegrable Fb volume 0 5 := by
    simpa only [Fb] using
      roughSaiasFullyRealIntegrand_intervalIntegrable hy hb.2
  have hqa : IntervalIntegrable qa volume 0 5 := by
    simpa only [qa] using
      roughSaiasDickmanDerivative_translate_intervalIntegrable ha.2
  have hqb : IntervalIntegrable qb volume 0 5 := by
    simpa only [qb] using
      roughSaiasDickmanDerivative_translate_intervalIntegrable hb.2
  have hdiff :
      (∫ v in (0 : ℝ)..5, Fa v) - ∫ v in (0 : ℝ)..5, Fb v =
        ∫ v in (0 : ℝ)..5, Fa v - Fb v :=
    (intervalIntegral.integral_sub hFa hFb).symm
  have hintegral :
      |(∫ v in (0 : ℝ)..5, Fa v) - ∫ v in (0 : ℝ)..5, Fb v| ≤
        ∫ v in (0 : ℝ)..5, |qa v - qb v| := by
    rw [hdiff]
    calc
      |(∫ v in (0 : ℝ)..5, Fa v - Fb v)| ≤
          ∫ v in (0 : ℝ)..5, |Fa v - Fb v| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ v in (0 : ℝ)..5, |qa v - qb v| := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hFa.sub hFb).abs (hqa.sub hqb).abs
        intro v hv
        have hweight := roughSaiasFullyRealFractionalWeight_mem_unitInterval
          hy.le hv.1
        change
          |qa v * roughSaiasFullyRealFractionalWeight y v -
              qb v * roughSaiasFullyRealFractionalWeight y v| ≤
            |qa v - qb v|
        rw [← sub_mul, abs_mul, abs_of_nonneg hweight.1]
        exact mul_le_of_le_one_right (abs_nonneg (qa v - qb v)) hweight.2
  have htranslate :
      (∫ v in (0 : ℝ)..5, |qa v - qb v|) ≤ 2 * |a - b| := by
    simpa only [qa, qb] using
      roughSaiasDickmanDerivative_translation_le_two_unconditional ha hb
  have hrho : |rho a - rho b| ≤ |a - b| :=
    roughRho_abs_sub_le_abs_of_le_five ha.2 hb.2
  change
    |(rho a - ∫ v in (0 : ℝ)..5, Fa v) -
      (rho b - ∫ v in (0 : ℝ)..5, Fb v)| ≤ 3 * |a - b|
  calc
    _ = |(rho a - rho b) -
        ((∫ v in (0 : ℝ)..5, Fa v) -
          ∫ v in (0 : ℝ)..5, Fb v)| := by
      congr 1
      ring
    _ ≤ |rho a - rho b| +
        |(∫ v in (0 : ℝ)..5, Fa v) -
          ∫ v in (0 : ℝ)..5, Fb v| := abs_sub _ _
    _ ≤ |a - b| + ∫ v in (0 : ℝ)..5, |qa v - qb v| :=
      add_le_add hrho hintegral
    _ ≤ |a - b| + 2 * |a - b| := add_le_add le_rfl htranslate
    _ = 3 * |a - b| := by ring

theorem roughSaiasFullyRealG_abs_le_sixteen
    {y u : ℝ} (hy : 1 < y) (hu : u ∈ Set.Icc (0 : ℝ) 5) :
    |roughSaiasFullyRealG y u| ≤ 16 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 5 := by norm_num
  have hlip := roughSaiasFullyRealG_lipschitz_three hy hu hzero
  rw [roughSaiasFullyRealG_eq_one_of_le_one (by norm_num : (0 : ℝ) ≤ 1)]
    at hlip
  calc
    |roughSaiasFullyRealG y u| =
        |(roughSaiasFullyRealG y u - 1) + 1| := by
      congr 1
      ring
    _ ≤ |roughSaiasFullyRealG y u - 1| + |(1 : ℝ)| := abs_add_le _ _
    _ ≤ 3 * |u - 0| + 1 := by
      rw [abs_one]
      exact add_le_add hlip le_rfl
    _ ≤ 3 * 5 + 1 := by
      have huabs : |u - 0| ≤ 5 := by
        rw [sub_zero, abs_of_nonneg hu.1]
        exact hu.2
      gcongr
    _ = 16 := by norm_num

/-- On the initial face the fully real normal form is exactly the natural
floor of its first argument. -/
theorem roughSaiasFullyRealLambdaNormalForm_eq_floor_of_le_one
    {x y : ℝ} (hx : 0 ≤ x)
    (hu1 : Real.log x / Real.log y ≤ 1) :
    roughSaiasFullyRealLambdaNormalForm x y = (((⌊x⌋₊ : ℕ) : ℝ)) := by
  unfold roughSaiasFullyRealLambdaNormalForm
  rw [roughSaiasFullyRealG_eq_one_of_le_one hu1,
    roughSaiasNatFloor_cast_eq_sub_fract hx]
  ring









/-! ## Exact Stieltjes identification at a real base -/

theorem roughSaiasRealStieltjesFractionalCorrection_eq_fullyRealBaseFree_of_ne
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (hne : t ≠ x / y) :
    roughSaiasRealStieltjesFractionalCorrection x y t =
      x * roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have hcoordNe : roughSaiasStieltjesCoordinate x y t ≠ 1 := by
    intro hcoord
    have hlogEq : Real.log x - Real.log t = Real.log y := by
      unfold roughSaiasStieltjesCoordinate at hcoord
      field_simp [hlogy] at hcoord
      linarith
    have hlogDiv : Real.log (x / y) = Real.log x - Real.log y := by
      rw [Real.log_div hx.ne' hypos.ne']
    have hlogs : Real.log t = Real.log (x / y) := by
      rw [hlogDiv]
      linarith
    have hexp := congrArg Real.exp hlogs
    rw [Real.exp_log ht, Real.exp_log (div_pos hx hypos)] at hexp
    exact hne hexp
  unfold roughSaiasRealStieltjesFractionalCorrection
    roughSaiasFullyRealBaseFreeFractionalKernel
  rw [roughSaiasOpenFaceDickmanDerivative_eq_roughSaias hcoordNe]
  unfold roughSaiasStieltjesCoordinate
  field_simp [ht.ne', hlogy]

theorem integrableOn_roughSaiasFullyRealStieltjesFractionalCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn (roughSaiasRealStieltjesFractionalCorrection x y)
      (Set.Ioc (1 : ℝ) x) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hcap := roughSaiasFullyReal_le_rpow_five hx hy hu5
  have hfull := roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
    (x := x) hy hu5
  have hcapInt : IntervalIntegrable
      (roughSaiasFullyRealBaseFreeFractionalKernel x y)
      volume (1 : ℝ) x := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le hx1, Set.uIcc_of_le (hx1.trans hcap)]
    exact Set.Icc_subset_Icc le_rfl hcap
  have hbaseIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hcapInt
  have hbaseIccMul : IntegrableOn
      (fun t : ℝ => x * roughSaiasFullyRealBaseFreeFractionalKernel x y t)
      (Set.Icc (1 : ℝ) x) :=
    hbaseIcc.const_mul x
  have hbase := hbaseIccMul.mono_set Set.Ioc_subset_Icc_self
  apply IntegrableOn.congr_fun_ae hbase
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [((volume : Measure ℝ).ae_ne (x / y))] with t hne ht
  exact (roughSaiasRealStieltjesFractionalCorrection_eq_fullyRealBaseFree_of_ne
    hx hy (zero_lt_one.trans ht.1) hne).symm

theorem integral_roughSaiasFullyRealStieltjesFractionalCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) x,
        roughSaiasRealStieltjesFractionalCorrection x y t) =
      x * roughSaiasFullyRealBaseFreeFractionalIntegral x y := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  rw [← intervalIntegral.integral_of_le hx1]
  have heq :
      (∫ t in (1 : ℝ)..x,
          roughSaiasRealStieltjesFractionalCorrection x y t) =
        ∫ t in (1 : ℝ)..x,
          x * roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [((volume : Measure ℝ).ae_ne (x / y))]
      with t hne ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    exact roughSaiasRealStieltjesFractionalCorrection_eq_fullyRealBaseFree_of_ne
      hx hy (zero_lt_one.trans_le htI.1) hne
  rw [heq, intervalIntegral.integral_const_mul,
    ← roughSaiasFullyRealBaseFreeIntegral_eq_realCap hx1 hy hu5]

/-- Every inner real-base Lambda produced by continuous Buchstab is the
literal fully real Saias normal form. -/
theorem roughSaiasLambdaStieltjes_eq_fullyRealNormalForm
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    roughSaiasLambdaStieltjes x y =
      roughSaiasFullyRealLambdaNormalForm x y := by
  have hsmooth := integrableOn_roughSaiasRealStieltjesSmoothCorrection
    hx1 hy hu5
  have hfract :=
    integrableOn_roughSaiasFullyRealStieltjesFractionalCorrection
      hx1 hy hu5
  have hsplit := MeasureTheory.integral_sub hsmooth hfract
  rw [roughSaiasLambdaStieltjes_eq_floor_add_floorCorrection
    hx1 hy hu5]
  have hpoint :
      (∫ t in Set.Ioc (1 : ℝ) x,
          roughSaiasRealStieltjesFloorCorrection x y t) =
        ∫ t in Set.Ioc (1 : ℝ) x,
          (roughSaiasRealStieltjesSmoothCorrection x y t -
            roughSaiasRealStieltjesFractionalCorrection x y t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact roughSaiasRealStieltjesFloorCorrection_eq_smooth_sub_fractional
      (zero_lt_one.trans ht.1) hy
  rw [hpoint, hsplit,
    integral_roughSaiasRealStieltjesSmoothCorrection hx1 hy hu5,
    integral_roughSaiasFullyRealStieltjesFractionalCorrection hx1 hy hu5]
  unfold roughSaiasFullyRealLambdaNormalForm
  rw [roughSaiasFullyRealG_eq_rho_sub_baseFree hy,
    roughSaiasNatFloor_cast_eq_sub_fract
      (zero_lt_one.trans_le hx1).le]
  ring



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFunctionalBuchstab -/
section


/-!
# Lifting pointwise continuous Buchstab through the finite signed functional

The pointwise identity in `RoughSaiasContinuousBuchstab` is now lifted
through the finite atom-minus-density functional.  The finite atomic swap is
proved unconditionally.  The density swap is stated with its exact compact
Fubini datum; that datum is ordinary product integrability of an explicit
bounded measurable kernel, not an endpoint or defect estimate.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full.DickmanBasic

noncomputable section





/-- The endpoint face bound propagates from `t=1` to every positive
Stieltjes variable `t≥1`. -/
theorem roughSaias_log_div_t_ratio_le
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y) (ht : 1 ≤ t)
    {A : ℝ} (hu : Real.log x / Real.log y ≤ A) :
    Real.log (x / t) / Real.log y ≤ A := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  rw [Real.log_div hx.ne' htpos.ne']
  apply (div_le_iff₀ hlogy).2
  have hu' := (div_le_iff₀ hlogy).1 hu
  linarith

/-! ## Discharging the compact Fubini datum -/

theorem measurable_uncurry_roughSaiasBuchstabDensityKernel (x : ℝ) :
    Measurable (Function.uncurry (roughSaiasBuchstabDensityKernel x)) := by
  have hxs : Measurable (fun p : ℝ × ℝ ↦ x / p.1) :=
    measurable_const.div measurable_fst
  have hquot : Measurable (fun p : ℝ × ℝ ↦ (x / p.1) / p.2) :=
    hxs.div measurable_snd
  have hcoord : Measurable (fun p : ℝ × ℝ ↦
      Real.log ((x / p.1) / p.2) / Real.log p.1) :=
    (Real.measurable_log.comp hquot).div
      (Real.measurable_log.comp measurable_fst)
  have hprofile : Measurable (fun p : ℝ × ℝ ↦
      (x / p.1) * roughSaiasZeroExtendedRho
        (Real.log ((x / p.1) / p.2) / Real.log p.1)) :=
    hxs.mul (measurable_roughSaiasZeroExtendedRho.comp hcoord)
  have hcontinuous : Measurable (fun p : ℝ × ℝ ↦
      ((x / p.1) * roughSaiasZeroExtendedRho
        (Real.log ((x / p.1) / p.2) / Real.log p.1)) /
          Real.log p.1) :=
    hprofile.div (Real.measurable_log.comp measurable_fst)
  simpa [Function.uncurry, roughSaiasBuchstabDensityKernel,
    roughSaiasContinuousBuchstabProfile,
    roughSaiasStieltjesDickmanProfile] using
      hcontinuous.mul (measurable_roughSaiasFloorDensity.comp measurable_snd)

/-- One finite constant controls the zero-extended finite Dickman profile
through the sixth face.  No positivity estimate on the sixth face is
needed: this is only compact boundedness of the continuous function `rho`.
-/
theorem exists_roughSaiasZeroExtendedRho_abs_bound_six :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, u ≤ 6 →
      |roughSaiasZeroExtendedRho u| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuous_rho.continuousOn (s := Set.Icc (0 : ℝ) 6)
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 6 := by norm_num
  have hC0 : 0 ≤ C :=
    (norm_nonneg (rho 0)).trans (hC 0 hzero)
  use C, hC0
  intro u hu6
  by_cases hu0 : u < 0
  · simp [roughSaiasZeroExtendedRho_of_neg hu0, hC0]
  · rw [roughSaiasZeroExtendedRho_of_nonneg (le_of_not_gt hu0)]
    simpa only [Real.norm_eq_abs] using
      hC u ⟨le_of_not_gt hu0, hu6⟩

theorem roughSaiasFloorDensity_mem_unitInterval
    {t : ℝ} (ht1 : 1 ≤ t) :
    0 ≤ roughSaiasFloorDensity t ∧ roughSaiasFloorDensity t ≤ 1 := by
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hfloor0 : (0 : ℝ) ≤ (((⌊t⌋₊ : ℕ) : ℝ)) := by positivity
  have hfloort : (((⌊t⌋₊ : ℕ) : ℝ)) ≤ t := Nat.floor_le ht.le
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  unfold roughSaiasFloorDensity
  constructor
  · exact div_nonneg hfloor0 ht2.le
  · apply (div_le_one ht2).2
    exact hfloort.trans (by nlinarith)

/-- If the base is enlarged from `y` to `b` and `t ≥ 1`, the supported
Dickman coordinate stays below the original sixth-face endpoint. -/
theorem roughSaias_profile_coordinate_le_six
    {x y b t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyb : y ≤ b) (ht1 : 1 ≤ t)
    (hu6 : Real.log x / Real.log y ≤ 6) :
    Real.log (x / t) / Real.log b ≤ 6 := by
  have hb : 1 < b := hy.trans_le hyb
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hq : 0 < x / t := div_pos hx ht
  by_cases hq1 : x / t ≤ 1
  · have hlogq : Real.log (x / t) ≤ 0 := Real.log_nonpos hq.le hq1
    have hlogb : 0 < Real.log b := Real.log_pos hb
    exact (div_nonpos_of_nonpos_of_nonneg hlogq hlogb.le).trans (by norm_num)
  · have hqone : 1 < x / t := lt_of_not_ge hq1
    have hlogq : 0 ≤ Real.log (x / t) := (Real.log_pos hqone).le
    have hlogyb : Real.log y ≤ Real.log b :=
      Real.log_le_log (zero_lt_one.trans hy) hyb
    calc
      Real.log (x / t) / Real.log b ≤
          Real.log (x / t) / Real.log y :=
        div_le_div_of_nonneg_left hlogq (Real.log_pos hy) hlogyb
      _ ≤ 6 := roughSaias_log_div_t_ratio_le hx hy ht1 hu6

theorem roughSaias_inner_profile_coordinate_le_six
    {x y s t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hys : y ≤ s) (ht1 : 1 ≤ t)
    (hu6 : Real.log x / Real.log y ≤ 6) :
    Real.log ((x / s) / t) / Real.log s ≤ 6 := by
  have hs : 1 < s := hy.trans_le hys
  have hspos : 0 < s := zero_lt_one.trans hs
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hq : 0 < x / t := div_pos hx ht
  have hquotient : (x / s) / t = (x / t) / s := by
    field_simp [hspos.ne', ht.ne']
  have hcoord :
      Real.log ((x / s) / t) / Real.log s =
        Real.log (x / t) / Real.log s - 1 := by
    rw [hquotient, Real.log_div hq.ne' hspos.ne']
    field_simp [(Real.log_pos hs).ne']
  rw [hcoord]
  have hbase := roughSaias_profile_coordinate_le_six
    hx hy hys ht1 hu6
  linarith

theorem integrableOn_roughSaiasProfile_mul_floorDensity_six
    {R : ℕ} {x y b : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyb : y ≤ b) (hu6 : Real.log x / Real.log y ≤ 6) :
    IntegrableOn
      (fun t ↦ roughSaiasStieltjesDickmanProfile x b t *
        roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (R : ℝ)) := by
  by_cases hR : 1 ≤ R
  · obtain ⟨C, hC0, hC⟩ :=
      exists_roughSaiasZeroExtendedRho_abs_bound_six
    have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hmeas : Measurable (fun t ↦
        roughSaiasStieltjesDickmanProfile x b t *
          roughSaiasFloorDensity t) :=
      (measurable_roughSaiasStieltjesDickmanProfile x b).mul
        measurable_roughSaiasFloorDensity
    have hconst : IntervalIntegrable (fun _ : ℝ ↦ x * C)
        volume (1 : ℝ) (R : ℝ) :=
      continuous_const.intervalIntegrable _ _
    have hint : IntervalIntegrable
        (fun t ↦ roughSaiasStieltjesDickmanProfile x b t *
          roughSaiasFloorDensity t)
        volume (1 : ℝ) (R : ℝ) := by
      apply hconst.mono_fun' hmeas.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t htU
      have htI : t ∈ Set.Icc (1 : ℝ) (R : ℝ) := by
        rw [← Set.uIcc_of_le hRreal]
        exact Set.uIoc_subset_uIcc htU
      have hcoord := roughSaias_profile_coordinate_le_six
        hx hy hyb htI.1 hu6
      have hdensity := roughSaiasFloorDensity_mem_unitInterval htI.1
      have hprofile :
          |roughSaiasStieltjesDickmanProfile x b t| ≤ x * C := by
        unfold roughSaiasStieltjesDickmanProfile
        rw [abs_mul, abs_of_pos hx]
        exact mul_le_mul_of_nonneg_left (hC _ hcoord) hx.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hdensity.1]
      calc
        |roughSaiasStieltjesDickmanProfile x b t| *
            roughSaiasFloorDensity t ≤
          (x * C) * 1 := mul_le_mul hprofile hdensity.2 hdensity.1
            (mul_nonneg hx.le hC0)
        _ = x * C := mul_one _
    have hintIcc :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hRreal).mp hint
    exact hintIcc.mono_set Set.Ioc_subset_Icc_self
  · have hR0 : R = 0 := by omega
    subst R
    simp

theorem roughSaiasBuchstabDensityKernel_abs_le
    {x y s t C : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hys : y ≤ s) (ht1 : 1 ≤ t)
    (hu6 : Real.log x / Real.log y ≤ 6) (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, u ≤ 6 → |roughSaiasZeroExtendedRho u| ≤ C) :
    |roughSaiasBuchstabDensityKernel x s t| ≤
      x * C / Real.log y := by
  have hs : 1 < s := hy.trans_le hys
  have hspos : 0 < s := zero_lt_one.trans hs
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogs : 0 < Real.log s := Real.log_pos hs
  have hlogys : Real.log y ≤ Real.log s :=
    Real.log_le_log (zero_lt_one.trans hy) hys
  have hxs : 0 ≤ x / s := (div_pos hx hspos).le
  have hxsle : x / s ≤ x := div_le_self hx.le hs.le
  have hcoord := roughSaias_inner_profile_coordinate_le_six
    hx hy hys ht1 hu6
  have hprofile :
      |roughSaiasStieltjesDickmanProfile (x / s) s t| ≤ x * C := by
    unfold roughSaiasStieltjesDickmanProfile
    rw [abs_mul, abs_of_nonneg hxs]
    calc
      (x / s) *
          |roughSaiasZeroExtendedRho
            (Real.log ((x / s) / t) / Real.log s)| ≤
        (x / s) * C := mul_le_mul_of_nonneg_left (hC _ hcoord) hxs
      _ ≤ x * C := mul_le_mul_of_nonneg_right hxsle hC0
  have hcontinuous :
      |roughSaiasContinuousBuchstabProfile x s t| ≤
        x * C / Real.log y := by
    unfold roughSaiasContinuousBuchstabProfile
    rw [abs_div, abs_of_pos hlogs]
    calc
      |roughSaiasStieltjesDickmanProfile (x / s) s t| / Real.log s ≤
          (x * C) / Real.log s :=
        div_le_div_of_nonneg_right hprofile hlogs.le
      _ ≤ x * C / Real.log y :=
        div_le_div_of_nonneg_left (mul_nonneg hx.le hC0) hlogy hlogys
  have hdensity := roughSaiasFloorDensity_mem_unitInterval ht1
  unfold roughSaiasBuchstabDensityKernel
  rw [abs_mul, abs_of_nonneg hdensity.1]
  calc
    |roughSaiasContinuousBuchstabProfile x s t| *
        roughSaiasFloorDensity t ≤
      (x * C / Real.log y) * 1 :=
        mul_le_mul hcontinuous hdensity.2 hdensity.1
          (div_nonneg (mul_nonneg hx.le hC0) hlogy.le)
    _ = x * C / Real.log y := mul_one _

theorem integrable_roughSaiasBuchstabDensityKernel
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (_hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    Integrable (Function.uncurry (roughSaiasBuchstabDensityKernel x))
      ((volume.restrict (Set.Ioc y z)).prod
        (volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ)))) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_roughSaiasZeroExtendedRho_abs_bound_six
  let μ : Measure ℝ := volume.restrict (Set.Ioc y z)
  let ν : Measure ℝ := volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ))
  let K : ℝ × ℝ → ℝ :=
    Function.uncurry (roughSaiasBuchstabDensityKernel x)
  have hmeas : Measurable K := by
    simpa [K] using measurable_uncurry_roughSaiasBuchstabDensityKernel x
  have hconst : Integrable
      (fun _ : ℝ × ℝ ↦ x * C / Real.log y) (μ.prod ν) := by
    exact integrable_const _
  have hbound : ∀ᵐ p ∂(μ.prod ν),
      ‖K p‖ ≤ x * C / Real.log y := by
    rw [Measure.ae_prod_iff_ae_ae
      (measurableSet_le hmeas.norm measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    simpa [K, Function.uncurry] using
      roughSaiasBuchstabDensityKernel_abs_le hx hy hs.1.le ht.1.le
        hu6 hC0 hC
  have hK : Integrable K (μ.prod ν) :=
    hconst.mono' hmeas.aestronglyMeasurable hbound
  simpa [μ, ν, K] using hK

/-- The compact Fubini datum is automatic under the pointwise sixth-face
hypotheses used by continuous Buchstab. -/
theorem roughSaiasBuchstabDensityFubini_of_compact
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    RoughSaiasBuchstabDensityFubini R x y z := by
  exact ⟨integrableOn_roughSaiasProfile_mul_floorDensity_six
      hx hy le_rfl hu6,
    integrableOn_roughSaiasProfile_mul_floorDensity_six
      hx hy hyz hu6,
    integrable_roughSaiasBuchstabDensityKernel hx hy hyz hu6⟩

/-- Division by a scalar commutes exactly with the finite signed
functional. -/
theorem roughSaiasFiniteStieltjesFunctional_div
    (R : ℕ) (f : ℝ → ℝ) (c : ℝ) :
    roughSaiasFiniteStieltjesFunctional R (fun t ↦ f t / c) =
      roughSaiasFiniteStieltjesFunctional R f / c := by
  have hatom : roughSaiasStieltjesAtomPart R (fun t ↦ f t / c) =
      roughSaiasStieltjesAtomPart R f / c := by
    unfold roughSaiasStieltjesAtomPart
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hdensity :
      roughSaiasStieltjesDensityPart R (fun t ↦ f t / c) =
        roughSaiasStieltjesDensityPart R f / c := by
    unfold roughSaiasStieltjesDensityPart
    calc
      (∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          (f t / c) * roughSaiasFloorDensity t) =
        ∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          c⁻¹ * (f t * roughSaiasFloorDensity t) := by
            apply integral_congr_ae
            filter_upwards with t
            ring
      _ = c⁻¹ * ∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          f t * roughSaiasFloorDensity t := by
            rw [MeasureTheory.integral_const_mul]
      _ = (∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          f t * roughSaiasFloorDensity t) / c := by ring
  unfold roughSaiasFiniteStieltjesFunctional
  rw [hatom, hdensity]
  ring

/-- At a fixed Buchstab base, the functional of the pointwise kernel is
the capped Stieltjes Lambda at `x/s`, divided by `log s`. -/
theorem roughSaiasFiniteStieltjesFunctional_buchstabProfile
    (R : ℕ) (x s : ℝ) :
    roughSaiasFiniteStieltjesFunctional R
        (roughSaiasContinuousBuchstabProfile x s) =
      roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
        Real.log s := by
  unfold roughSaiasContinuousBuchstabProfile
    roughSaiasLambdaStieltjesWithCutoff
  exact roughSaiasFiniteStieltjesFunctional_div R
    (roughSaiasStieltjesDickmanProfile (x / s) s) (Real.log s)

/-! ## The finite atomic lift -/

/-- Finite atoms commute with continuous Buchstab, including the finite
sum/integral interchange. -/
theorem roughSaiasStieltjesAtomPart_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    roughSaiasStieltjesAtomPart R
        (roughSaiasStieltjesDickmanProfile x y) =
      roughSaiasStieltjesAtomPart R
          (roughSaiasStieltjesDickmanProfile x z) -
        ∫ s in y..z,
          roughSaiasStieltjesAtomPart R
            (roughSaiasContinuousBuchstabProfile x s) := by
  have hface (n : ℕ) (hn : n ∈ Finset.Icc 1 R) :
      Real.log (x / (n : ℝ)) / Real.log y ≤ 6 :=
    roughSaias_log_div_t_ratio_le hx hy
      (by exact_mod_cast (Finset.mem_Icc.mp hn).1) hu6
  have hnpos (n : ℕ) (hn : n ∈ Finset.Icc 1 R) : 0 < n := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    omega
  have hint (n : ℕ) (hn : n ∈ Finset.Icc 1 R) :
      IntervalIntegrable
        (fun s ↦ roughSaiasContinuousBuchstabProfile x s (n : ℝ) /
          (n : ℝ)) volume y z :=
    (intervalIntegrable_roughSaiasContinuousBuchstabProfile hx
      (by exact_mod_cast (hnpos n hn)) hy hyz (hface n hn)).div_const _
  unfold roughSaiasStieltjesAtomPart
  calc
    (∑ n ∈ Finset.Icc 1 R,
        roughSaiasStieltjesDickmanProfile x y (n : ℝ) / (n : ℝ)) =
      ∑ n ∈ Finset.Icc 1 R,
        (roughSaiasStieltjesDickmanProfile x z (n : ℝ) / (n : ℝ) -
          ∫ s in y..z,
            roughSaiasContinuousBuchstabProfile x s (n : ℝ) /
              (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [roughSaiasStieltjesDickmanProfile_buchstab hx
        (by exact_mod_cast (hnpos n hn)) hy hyz (hface n hn),
        intervalIntegral.integral_div]
      ring
    _ = (∑ n ∈ Finset.Icc 1 R,
          roughSaiasStieltjesDickmanProfile x z (n : ℝ) / (n : ℝ)) -
        ∑ n ∈ Finset.Icc 1 R,
          ∫ s in y..z,
            roughSaiasContinuousBuchstabProfile x s (n : ℝ) /
              (n : ℝ) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ n ∈ Finset.Icc 1 R,
          roughSaiasStieltjesDickmanProfile x z (n : ℝ) / (n : ℝ)) -
        ∫ s in y..z,
          ∑ n ∈ Finset.Icc 1 R,
            roughSaiasContinuousBuchstabProfile x s (n : ℝ) /
              (n : ℝ) := by
      rw [intervalIntegral.integral_finset_sum hint]

/-! ## The density Fubini lift -/

/-- The absolutely continuous density commutes with continuous Buchstab
under its explicit compact Fubini datum. -/
theorem roughSaiasStieltjesDensityPart_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6)
    (hFubini : RoughSaiasBuchstabDensityFubini R x y z) :
    roughSaiasStieltjesDensityPart R
        (roughSaiasStieltjesDickmanProfile x y) =
      roughSaiasStieltjesDensityPart R
          (roughSaiasStieltjesDickmanProfile x z) -
        ∫ s in y..z,
          roughSaiasStieltjesDensityPart R
            (roughSaiasContinuousBuchstabProfile x s) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc y z)
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ))
  let K : ℝ × ℝ → ℝ :=
    Function.uncurry (roughSaiasBuchstabDensityKernel x)
  have hK : Integrable K (μ.prod ν) := by
    simpa [μ, ν, K] using hFubini.2.2
  have hinnerT : Integrable
      (fun t ↦ ∫ s, K (s, t) ∂μ) ν := hK.integral_prod_right
  have hzInt := hFubini.2.1
  have hpoint : ∀ᵐ t ∂ν,
      roughSaiasStieltjesDickmanProfile x y t *
          roughSaiasFloorDensity t =
        roughSaiasStieltjesDickmanProfile x z t *
            roughSaiasFloorDensity t -
          ∫ s, K (s, t) ∂μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := zero_lt_one.trans ht.1
    have hface := roughSaias_log_div_t_ratio_le hx hy ht.1.le hu6
    have hbuch := roughSaiasStieltjesDickmanProfile_buchstab
      hx htpos hy hyz hface
    rw [intervalIntegral.integral_of_le hyz] at hbuch
    change roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t =
      roughSaiasStieltjesDickmanProfile x z t *
          roughSaiasFloorDensity t -
        ∫ s in Set.Ioc y z,
          roughSaiasBuchstabDensityKernel x s t
    rw [hbuch]
    unfold roughSaiasBuchstabDensityKernel
    rw [MeasureTheory.integral_mul_const]
    ring
  unfold roughSaiasStieltjesDensityPart
  have hleft :
      (∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          roughSaiasStieltjesDickmanProfile x y t *
            roughSaiasFloorDensity t) =
        ∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          (roughSaiasStieltjesDickmanProfile x z t *
              roughSaiasFloorDensity t -
            ∫ s, K (s, t) ∂μ) :=
    by simpa [ν] using integral_congr_ae hpoint
  rw [hleft, MeasureTheory.integral_sub hzInt
    (by simpa [ν] using hinnerT)]
  have hswap : (∫ s, ∫ t, K (s, t) ∂ν ∂μ) =
      ∫ t, ∫ s, K (s, t) ∂μ ∂ν := by
    apply integral_integral_swap
    simpa only [Function.uncurry_apply_pair, Prod.eta] using hK
  rw [← hswap]
  rw [intervalIntegral.integral_of_le hyz]
  rfl

/-! ## Functional continuous Buchstab -/

private theorem intervalIntegrable_roughSaiasStieltjesAtomPart_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    IntervalIntegrable
      (fun s ↦ roughSaiasStieltjesAtomPart R
        (roughSaiasContinuousBuchstabProfile x s)) volume y z := by
  unfold roughSaiasStieltjesAtomPart
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 R) :
      IntervalIntegrable
        (fun s ↦ roughSaiasContinuousBuchstabProfile x s (n : ℝ) /
          (n : ℝ)) volume y z := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn1real : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn1
    have hface := roughSaias_log_div_t_ratio_le hx hy
      hn1real hu6
    have hnposreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    exact (intervalIntegrable_roughSaiasContinuousBuchstabProfile hx
      hnposreal hy hyz hface).div_const _
  apply (IntervalIntegrable.sum (Finset.Icc 1 R) hterm).congr
  intro s _hs
  simp only [Finset.sum_apply]

/-- The capped Lambda integrand occurring in functional Buchstab is
interval-integrable; the product-kernel proof discharges the density part. -/
theorem intervalIntegrable_roughSaiasLambdaStieltjesWithCutoff_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    IntervalIntegrable
      (fun s ↦ roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
        Real.log s) volume y z := by
  have hAtom :=
    intervalIntegrable_roughSaiasStieltjesAtomPart_buchstab
      (R := R) hx hy hyz hu6
  have hK := integrable_roughSaiasBuchstabDensityKernel
    (R := R) hx hy hyz hu6
  have hDensityOn : IntegrableOn
      (fun s ↦ roughSaiasStieltjesDensityPart R
        (roughSaiasContinuousBuchstabProfile x s)) (Set.Ioc y z) := by
    simpa [roughSaiasStieltjesDensityPart,
      roughSaiasBuchstabDensityKernel, Function.uncurry] using
        hK.integral_prod_left
  have hDensity : IntervalIntegrable
      (fun s ↦ roughSaiasStieltjesDensityPart R
        (roughSaiasContinuousBuchstabProfile x s)) volume y z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hyz).mpr hDensityOn
  have hFunctional : IntervalIntegrable
      (fun s ↦ roughSaiasFiniteStieltjesFunctional R
        (roughSaiasContinuousBuchstabProfile x s)) volume y z := by
    unfold roughSaiasFiniteStieltjesFunctional
    exact hAtom.sub hDensity
  apply hFunctional.congr
  intro s _hs
  exact roughSaiasFiniteStieltjesFunctional_buchstabProfile R x s

/-- Exact continuous Buchstab identity for the finite signed functional. -/
theorem roughSaiasFiniteStieltjesFunctional_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6)
    (hFubini : RoughSaiasBuchstabDensityFubini R x y z) :
    roughSaiasFiniteStieltjesFunctional R
        (roughSaiasStieltjesDickmanProfile x y) =
      roughSaiasFiniteStieltjesFunctional R
          (roughSaiasStieltjesDickmanProfile x z) -
        ∫ s in y..z,
          roughSaiasFiniteStieltjesFunctional R
            (roughSaiasContinuousBuchstabProfile x s) := by
  have hatom := roughSaiasStieltjesAtomPart_buchstab
    (R := R) hx hy hyz hu6
  have hdensity := roughSaiasStieltjesDensityPart_buchstab
    (R := R) hx hy hyz hu6 hFubini
  have hAtomInt :=
    intervalIntegrable_roughSaiasStieltjesAtomPart_buchstab
      (R := R) hx hy hyz hu6
  have hK : Integrable
      (Function.uncurry (roughSaiasBuchstabDensityKernel x))
      ((volume.restrict (Set.Ioc y z)).prod
        (volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ)))) := hFubini.2.2
  have hDensityOn : IntegrableOn
      (fun s ↦ roughSaiasStieltjesDensityPart R
        (roughSaiasContinuousBuchstabProfile x s)) (Set.Ioc y z) := by
    simpa [roughSaiasStieltjesDensityPart,
      roughSaiasBuchstabDensityKernel, Function.uncurry] using
        hK.integral_prod_left
  have hDensityInt : IntervalIntegrable
      (fun s ↦ roughSaiasStieltjesDensityPart R
        (roughSaiasContinuousBuchstabProfile x s)) volume y z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hyz).mpr hDensityOn
  unfold roughSaiasFiniteStieltjesFunctional
  rw [hatom, hdensity,
    intervalIntegral.integral_sub hAtomInt hDensityInt]
  ring

/-- The usual Lambda-shaped form of functional Buchstab. -/
theorem roughSaiasLambdaStieltjesWithCutoff_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6)
    (hFubini : RoughSaiasBuchstabDensityFubini R x y z) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjesWithCutoff R x z -
        ∫ s in y..z,
          roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
            Real.log s := by
  unfold roughSaiasLambdaStieltjesWithCutoff
  rw [roughSaiasFiniteStieltjesFunctional_buchstab
    hx hy hyz hu6 hFubini]
  apply congrArg (fun q : ℝ ↦
    roughSaiasFiniteStieltjesFunctional R
        (roughSaiasStieltjesDickmanProfile x z) - q)
  apply intervalIntegral.integral_congr
  intro s hs
  exact roughSaiasFiniteStieltjesFunctional_buchstabProfile R x s





/-- Continuous Buchstab for the capped Stieltjes Lambda, with every
compact integrability and Fubini obligation proved internally. -/
theorem roughSaiasLambdaStieltjesWithCutoff_buchstab_unconditional
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjesWithCutoff R x z -
        ∫ s in y..z,
          roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
            Real.log s := by
  exact roughSaiasLambdaStieltjesWithCutoff_buchstab hx hy hyz hu6
    (roughSaiasBuchstabDensityFubini_of_compact hx hy hyz hu6)

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFullyRealBuchstabCells -/
section


/-!
# Unit-cell decomposition of the fully real Buchstab integral

The functional continuous-Buchstab identity is converted here into the
project's natural-base normal forms.  On a cell `s ∈ [m,m+1]`, the inner
term is split exactly into

* quotient drift at the current real base `s`, and
* real-base drift from `s` to the natural endpoint `m+1`.

No equality between the real and natural bases is left as a premise.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full

noncomputable section





/-- Above the square-root transition the fully real inner normal form is
on its initial face, hence is exactly the real quotient selector. -/
theorem roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector
    {X : ℕ} {s : ℝ} (hX : 0 < X) (hs : 1 < s)
    (hupper : (X : ℝ) ≤ s ^ 2) :
    roughSaiasFullyRealBuchstabNormalIntegrand X s =
      roughSaiasRealQuotientSelectorIntegrand X s := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hspos : 0 < s := zero_lt_one.trans hs
  have hqpos : 0 < (X : ℝ) / s := div_pos hXR hspos
  have hqs : (X : ℝ) / s ≤ s := by
    apply (div_le_iff₀ hspos).2
    simpa [pow_two] using hupper
  have hlogq : Real.log ((X : ℝ) / s) ≤ Real.log s :=
    Real.log_le_log hqpos hqs
  have hcoord : Real.log ((X : ℝ) / s) / Real.log s ≤ 1 :=
    (div_le_one (Real.log_pos hs)).2 hlogq
  unfold roughSaiasFullyRealBuchstabNormalIntegrand
    roughSaiasRealQuotientSelectorIntegrand
  rw [roughSaiasFullyRealLambdaNormalForm_eq_floor_of_le_one
    hqpos.le hcoord]

theorem roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector_on_cell
    {X m : ℕ} (hX : 0 < X) (hm2 : 2 ≤ m)
    (hupper : X ≤ m ^ 2) {s : ℝ}
    (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ)) :
    roughSaiasFullyRealBuchstabNormalIntegrand X s =
      roughSaiasRealQuotientSelectorIntegrand X s := by
  have hms : (m : ℝ) ≤ s := hs.1
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hs2 : (m : ℝ) ^ 2 ≤ s ^ 2 := by nlinarith
  have hupperR : (X : ℝ) ≤ s ^ 2 :=
    (by exact_mod_cast hupper : (X : ℝ) ≤ (m : ℝ) ^ 2).trans hs2
  have hsone : 1 < s :=
    (by exact_mod_cast (show 1 < m by omega) : (1 : ℝ) < (m : ℝ)).trans_le hs.1
  exact roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector
    hX hsone hupperR

/-- On the natural range `y ≤ s ≤ Z ≤ X`, the fixed outer cutoff
`X` is canonical for the inner Stieltjes functional, and the latter is the
fully real normal form. -/
theorem roughSaiasLambdaStieltjesWithCutoff_inner_eq_fullyReal
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    {s : ℝ} (hs : s ∈ Set.Icc (y : ℝ) (Z : ℝ)) :
    roughSaiasLambdaStieltjesWithCutoff X ((X : ℝ) / s) s =
      roughSaiasFullyRealLambdaNormalForm ((X : ℝ) / s) s := by
  have hyone : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hsone : 1 < s := hyone.trans_le hs.1
  have hspos : 0 < s := zero_lt_one.trans hsone
  have hXposNat : 0 < X := by omega
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast hXposNat
  have hsX : s ≤ (X : ℝ) :=
    hs.2.trans (by exact_mod_cast hZX)
  have hinnerPos : 0 < (X : ℝ) / s := div_pos hXpos hspos
  have hinnerOne : 1 ≤ (X : ℝ) / s :=
    (one_le_div hspos).2 hsX
  have hinnerCap : (X : ℝ) / s ≤ (X : ℝ) :=
    div_le_self hXpos.le hsone.le
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hyone
  have hlogs : 0 < Real.log s := Real.log_pos hsone
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogys : Real.log (y : ℝ) ≤ Real.log s :=
    Real.log_le_log (zero_lt_one.trans hyone) hs.1
  have hratio : Real.log (X : ℝ) / Real.log s ≤ 5 :=
    (div_le_div_of_nonneg_left hlogX0 hlogy hlogys).trans hu5
  have hinnerFace :
      Real.log ((X : ℝ) / s) / Real.log s ≤ 5 := by
    rw [Real.log_div hXpos.ne' hspos.ne']
    calc
      (Real.log (X : ℝ) - Real.log s) / Real.log s =
          Real.log (X : ℝ) / Real.log s - 1 := by
        field_simp [hlogs.ne']
      _ ≤ 5 := by linarith
  rw [roughSaiasLambdaStieltjesWithCutoff_eq_canonical
    hinnerPos hsone hinnerCap]
  exact roughSaiasLambdaStieltjes_eq_fullyRealNormalForm
    hinnerOne hsone hinnerFace

/-- Exact continuous Buchstab for natural outer endpoints, with every
inner term expressed in the fully real Saias normal form. -/
theorem roughSaiasNaturalMain_buchstab_fullyReal
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalMain X y =
      roughSaiasNaturalMain X Z -
        ∫ s in (y : ℝ)..(Z : ℝ),
          roughSaiasFullyRealBuchstabNormalIntegrand X s := by
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hyone : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hyZR : (y : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hyZ
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hZone : 1 < (Z : ℝ) := hyone.trans_le hyZR
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos hyone
  have hlogyZ : Real.log (y : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log (zero_lt_one.trans hyone) hyZR
  have hu5Z : Real.log (X : ℝ) / Real.log (Z : ℝ) ≤ 5 :=
    (div_le_div_of_nonneg_left hlogX0 hlogy hlogyZ).trans hu5
  have hbuch := roughSaiasLambdaStieltjesWithCutoff_buchstab_unconditional
    (R := X) (x := (X : ℝ)) (y := (y : ℝ)) (z := (Z : ℝ))
    hXpos hyone hyZR (hu5.trans (by norm_num))
  have hyEndpoint :
      roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) (y : ℝ) =
        roughSaiasNaturalMain X y := by
    rw [← roughSaiasLambdaStieltjes_nat X (y : ℝ),
      roughSaiasLambdaStieltjes_nat_eq_normalForm
        (show 1 ≤ X by omega) hy2 hu5,
      roughSaiasNaturalMain_eq_lambdaNormalForm]
  have hZEndpoint :
      roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) (Z : ℝ) =
        roughSaiasNaturalMain X Z := by
    rw [← roughSaiasLambdaStieltjes_nat X (Z : ℝ),
      roughSaiasLambdaStieltjes_nat_eq_normalForm
        (show 1 ≤ X by omega) (by omega) hu5Z,
      roughSaiasNaturalMain_eq_lambdaNormalForm]
  have hinner :
      (∫ s in (y : ℝ)..(Z : ℝ),
          roughSaiasLambdaStieltjesWithCutoff X ((X : ℝ) / s) s /
            Real.log s) =
        ∫ s in (y : ℝ)..(Z : ℝ),
          roughSaiasFullyRealBuchstabNormalIntegrand X s := by
    apply intervalIntegral.integral_congr
    intro s hsU
    have hsI : s ∈ Set.Icc (y : ℝ) (Z : ℝ) := by
      simpa [Set.uIcc_of_le hyZR] using hsU
    unfold roughSaiasFullyRealBuchstabNormalIntegrand
    change
      roughSaiasLambdaStieltjesWithCutoff X ((X : ℝ) / s) s /
          Real.log s =
        roughSaiasFullyRealLambdaNormalForm ((X : ℝ) / s) s /
          Real.log s
    rw [roughSaiasLambdaStieltjesWithCutoff_inner_eq_fullyReal
      hy2 hyZ hZX hu5 hsI]
  rw [hyEndpoint, hZEndpoint, hinner] at hbuch
  exact hbuch

theorem intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    IntervalIntegrable
      (roughSaiasFullyRealBuchstabNormalIntegrand X)
      volume (y : ℝ) (Z : ℝ) := by
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hyone : 1 < (y : ℝ) := by
    exact_mod_cast (show 1 < y by omega)
  have hyZR : (y : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hyZ
  have hcap :=
    intervalIntegrable_roughSaiasLambdaStieltjesWithCutoff_buchstab
      (R := X) hXpos hyone hyZR (hu5.trans (by norm_num))
  apply hcap.congr
  intro s hsU
  have hsI : s ∈ Set.Icc (y : ℝ) (Z : ℝ) := by
    have hsU' : s ∈ Set.uIcc (y : ℝ) (Z : ℝ) :=
      Set.uIoc_subset_uIcc hsU
    simpa [Set.uIcc_of_le hyZR] using hsU'
  unfold roughSaiasFullyRealBuchstabNormalIntegrand
  change
    roughSaiasLambdaStieltjesWithCutoff X ((X : ℝ) / s) s /
        Real.log s =
      roughSaiasFullyRealLambdaNormalForm ((X : ℝ) / s) s /
        Real.log s
  rw [roughSaiasLambdaStieltjesWithCutoff_inner_eq_fullyReal
    hy2 hyZ hZX hu5 hsI]

/-! ## Natural unit cells -/

theorem integral_roughSaiasFullyRealBuchstab_eq_sum_cells
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    (∫ s in (y : ℝ)..(Z : ℝ),
        roughSaiasFullyRealBuchstabNormalIntegrand X s) =
      ∑ m ∈ Finset.Ico y Z,
        ∫ s in (m : ℝ)..(m + 1 : ℕ),
          roughSaiasFullyRealBuchstabNormalIntegrand X s := by
  have hglobal :=
    intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
      hy2 hyZ hZX hu5
  have hint : ∀ m ∈ Finset.Ico y Z,
      IntervalIntegrable (roughSaiasFullyRealBuchstabNormalIntegrand X)
        volume (m : ℝ) (m + 1 : ℕ) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hsubset : Set.uIcc (m : ℝ) (m + 1 : ℕ) ⊆
        Set.uIcc (y : ℝ) (Z : ℝ) := by
      rw [Set.uIcc_of_le (by norm_num : (m : ℝ) ≤ (m + 1 : ℕ)),
        Set.uIcc_of_le (by exact_mod_cast hyZ)]
      exact Set.Icc_subset_Icc
        (by exact_mod_cast hmData.1) (by exact_mod_cast (show m + 1 ≤ Z by omega))
    exact hglobal.mono_set hsubset
  symm
  exact intervalIntegral.sum_integral_adjacent_intervals_Ico hyZ
    (fun m hm ↦ hint m (Finset.mem_Ico.mpr hm))

/-- Right-endpoint sample on a unit cell, in the existing natural-base
theta weight. -/
theorem roughSaiasFullyRealBuchstabNormalIntegrand_nat
    (X m : ℕ) :
    roughSaiasFullyRealBuchstabNormalIntegrand X (m : ℝ) =
      roughSaiasNormalFormThetaWeight X m := by
  unfold roughSaiasFullyRealBuchstabNormalIntegrand
    roughSaiasNormalFormThetaWeight roughSaiasContinuousPrimeNormalForm
  rw [roughSaiasFullyRealLambdaNormalForm_nat]

theorem roughSaiasNormalFormThetaWeight_eq_selector_of_sq_le
    {X m : ℕ} (hX : 0 < X) (hm2 : 2 ≤ m) (hupper : X ≤ m ^ 2) :
    roughSaiasNormalFormThetaWeight X (m + 1) =
      roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ) := by
  rw [← roughSaiasFullyRealBuchstabNormalIntegrand_nat]
  apply roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector
  · exact hX
  · exact_mod_cast (show 1 < m + 1 by omega)
  · have hmle : m ^ 2 ≤ (m + 1) ^ 2 := by nlinarith
    exact_mod_cast hupper.trans hmle









/-- On an upper selector cell, the real-base remainder has no hidden `G`:
it is exactly the quotient-selector quadrature error. -/
theorem roughSaiasFullyRealBuchstabCellRemainder_eq_selector
    {X m : ℕ} (hX : 0 < X) (hm2 : 2 ≤ m) (hupper : X ≤ m ^ 2) :
    roughSaiasFullyRealBuchstabCellRemainder X m =
      ∫ s in (m : ℝ)..(m + 1 : ℕ),
        (roughSaiasRealQuotientSelectorIntegrand X s -
          roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ)) := by
  unfold roughSaiasFullyRealBuchstabCellRemainder
  apply intervalIntegral.integral_congr
  intro s hsU
  have hsI : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ) := by
    simpa [Set.uIcc_of_le
      (by norm_num : (m : ℝ) ≤ (m + 1 : ℕ))] using hsU
  change
    roughSaiasFullyRealBuchstabNormalIntegrand X s -
        roughSaiasNormalFormThetaWeight X (m + 1) =
      roughSaiasRealQuotientSelectorIntegrand X s -
        roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ)
  rw [roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector_on_cell
      hX hm2 hupper hsI,
    roughSaiasNormalFormThetaWeight_eq_selector_of_sq_le hX hm2 hupper]

/-- Pointwise right-endpoint quadrature bound for the quotient selector.
The first term is the exact natural quotient drop; hence its sum telescopes.
The second is only the variation of `1/log`. -/
theorem roughSaiasRealQuotientSelector_cell_sub_right_abs_le
    {X m : ℕ} (hm2 : 2 ≤ m) {s : ℝ}
    (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ)) :
    |roughSaiasRealQuotientSelectorIntegrand X s -
        roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ)| ≤
      (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
          Real.log (m : ℝ) +
        ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) := by
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hmpos : 0 < (m : ℝ) := zero_lt_one.trans hmone
  have hspos : 0 < s := hmpos.trans_le hs.1
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hrealLower :
      (X : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ (X : ℝ) / s :=
    div_le_div_of_nonneg_left hX0 hspos hs.2
  have hrealUpper :
      (X : ℝ) / s ≤ (X : ℝ) / (m : ℝ) :=
    div_le_div_of_nonneg_left hX0 hmpos hs.1
  have hfloorLower := Nat.floor_le_floor hrealLower
  have hfloorUpper := Nat.floor_le_floor hrealUpper
  rw [Nat.floor_div_eq_div] at hfloorLower hfloorUpper
  let A : ℝ := (((⌊(X : ℝ) / s⌋₊ : ℕ) : ℝ))
  let q₀ : ℝ := ((X / m : ℕ) : ℝ)
  let q₁ : ℝ := ((X / (m + 1) : ℕ) : ℝ)
  have hq₁A : q₁ ≤ A := by
    dsimp [q₁, A]
    exact_mod_cast hfloorLower
  have hAq₀ : A ≤ q₀ := by
    dsimp [A, q₀]
    exact_mod_cast hfloorUpper
  have hq₁0 : 0 ≤ q₁ := by positivity
  have hq₁q₀ : q₁ ≤ q₀ := hq₁A.trans hAq₀
  have hLm : 0 < Real.log (m : ℝ) := Real.log_pos hmone
  have hsone : 1 < s := hmone.trans_le hs.1
  have hLs : 0 < Real.log s := Real.log_pos hsone
  have hLmLs : Real.log (m : ℝ) ≤ Real.log s :=
    Real.log_le_log hmpos hs.1
  have hLsL1 : Real.log s ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log hspos hs.2
  have hInvLmLs : 1 / Real.log s ≤ 1 / Real.log (m : ℝ) :=
    one_div_le_one_div_of_le hLm hLmLs
  have hselectorNonneg :
      0 ≤ A / Real.log s - q₁ / Real.log ((m + 1 : ℕ) : ℝ) := by
    have hleft : q₁ / Real.log ((m + 1 : ℕ) : ℝ) ≤
        q₁ / Real.log s :=
      div_le_div_of_nonneg_left hq₁0 hLs hLsL1
    have hright : q₁ / Real.log s ≤ A / Real.log s :=
      div_le_div_of_nonneg_right hq₁A hLs.le
    linarith
  have hfirst :
      (A - q₁) / Real.log s ≤
        (q₀ - q₁) / Real.log (m : ℝ) := by
    calc
      (A - q₁) / Real.log s ≤
          (q₀ - q₁) / Real.log s :=
        div_le_div_of_nonneg_right (sub_le_sub_right hAq₀ q₁) hLs.le
      _ ≤ (q₀ - q₁) / Real.log (m : ℝ) :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hq₁q₀) hLm hLmLs
  have hsecond :
      q₁ * (1 / Real.log s -
          1 / Real.log ((m + 1 : ℕ) : ℝ)) ≤
        q₁ * (1 / Real.log (m : ℝ) -
          1 / Real.log ((m + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left
      (sub_le_sub_right hInvLmLs _ ) hq₁0
  unfold roughSaiasRealQuotientSelectorIntegrand
  rw [Nat.floor_div_eq_div]
  change |A / Real.log s - q₁ / Real.log ((m + 1 : ℕ) : ℝ)| ≤ _
  rw [abs_of_nonneg hselectorNonneg]
  calc
    A / Real.log s - q₁ / Real.log ((m + 1 : ℕ) : ℝ) =
        (A - q₁) / Real.log s +
          q₁ * (1 / Real.log s -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) := by ring
    _ ≤ (q₀ - q₁) / Real.log (m : ℝ) +
        q₁ * (1 / Real.log (m : ℝ) -
          1 / Real.log ((m + 1 : ℕ) : ℝ)) :=
      add_le_add hfirst hsecond
    _ = (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
          Real.log (m : ℝ) +
        ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) := by rfl

theorem roughSaiasFullyRealBuchstabCellRemainder_abs_le_selectorLedger
    {X m : ℕ} (hX : 0 < X) (hm2 : 2 ≤ m) (hupper : X ≤ m ^ 2) :
    |roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
          Real.log (m : ℝ) +
        ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) := by
  rw [roughSaiasFullyRealBuchstabCellRemainder_eq_selector hX hm2 hupper]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s : ℝ ↦
      roughSaiasRealQuotientSelectorIntegrand X s -
        roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ))
    (C :=
      (((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)) /
          Real.log (m : ℝ) +
        ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)))
    (a := (m : ℝ)) (b := (m + 1 : ℕ)) (fun s hs ↦ by
      rw [Real.norm_eq_abs]
      apply roughSaiasRealQuotientSelector_cell_sub_right_abs_le hm2
      have hs' := Set.uIoc_subset_uIcc hs
      simpa [Set.uIcc_of_le
        (by norm_num : (m : ℝ) ≤ (m + 1 : ℕ))] using hs')
  simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_left, abs_one, mul_one] using hnorm



theorem abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_selectorLedger
    {X M Z : ℕ} (hX : 0 < X) (hM2 : 2 ≤ M)
    (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      ∑ m ∈ Finset.Ico M Z, roughSaiasSelectorCellLedger X m := by
  calc
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      ∑ m ∈ Finset.Ico M Z,
        |roughSaiasFullyRealBuchstabCellRemainder X m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Ico M Z,
        roughSaiasSelectorCellLedger X m := by
      apply Finset.sum_le_sum
      intro m hm
      have hmData := Finset.mem_Ico.mp hm
      have hm2 : 2 ≤ m := hM2.trans hmData.1
      have hMmSq : M ^ 2 ≤ m ^ 2 := by nlinarith
      have hXmSq : X ≤ m ^ 2 := hupper.trans hMmSq
      simpa [roughSaiasSelectorCellLedger] using
        roughSaiasFullyRealBuchstabCellRemainder_abs_le_selectorLedger
          hX hm2 hXmSq



theorem integral_roughSaiasFullyRealBuchstab_cell_eq_sample_add_remainder
    {X y Z m : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hm : m ∈ Finset.Ico y Z) :
    (∫ s in (m : ℝ)..(m + 1 : ℕ),
        roughSaiasFullyRealBuchstabNormalIntegrand X s) =
      roughSaiasNormalFormThetaWeight X (m + 1) +
        roughSaiasFullyRealBuchstabCellRemainder X m := by
  have hmData := Finset.mem_Ico.mp hm
  have hmle : m ≤ m + 1 := by omega
  have hym : y ≤ m := hmData.1
  have hmZ : m + 1 ≤ Z := by omega
  have hglobal :=
    intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
      hy2 hyZ hZX hu5
  have hsubset : Set.uIcc (m : ℝ) (m + 1 : ℕ) ⊆
      Set.uIcc (y : ℝ) (Z : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hmle),
      Set.uIcc_of_le (by exact_mod_cast hyZ)]
    exact Set.Icc_subset_Icc (by exact_mod_cast hym) (by exact_mod_cast hmZ)
  have hcell := hglobal.mono_set hsubset
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ roughSaiasNormalFormThetaWeight X (m + 1))
      volume (m : ℝ) (m + 1 : ℕ) :=
    continuous_const.intervalIntegrable _ _
  unfold roughSaiasFullyRealBuchstabCellRemainder
  rw [intervalIntegral.integral_sub hcell hconst]
  simp

/-- The natural endpoint difference is the discrete right-endpoint main
term plus the exact fully real cell remainders. -/
theorem roughSaiasNaturalMain_buchstab_sum_cells
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalMain X y =
      roughSaiasNaturalMain X Z -
        (FriableAsymptotic.integerAbelMain
          (roughSaiasNormalFormThetaWeight X) y Z +
          ∑ m ∈ Finset.Ico y Z,
            roughSaiasFullyRealBuchstabCellRemainder X m) := by
  have hcontinuous := roughSaiasNaturalMain_buchstab_fullyReal
    hy2 hyZ.le hZX hu5
  rw [integral_roughSaiasFullyRealBuchstab_eq_sum_cells
      hy2 hyZ.le hZX hu5]
    at hcontinuous
  have hcells :
      (∑ m ∈ Finset.Ico y Z,
          ∫ s in (m : ℝ)..(m + 1 : ℕ),
            roughSaiasFullyRealBuchstabNormalIntegrand X s) =
        ∑ m ∈ Finset.Ico y Z,
          (roughSaiasNormalFormThetaWeight X (m + 1) +
            roughSaiasFullyRealBuchstabCellRemainder X m) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact integral_roughSaiasFullyRealBuchstab_cell_eq_sample_add_remainder
      hy2 hyZ.le hZX hu5 hm
  rw [hcells, Finset.sum_add_distrib] at hcontinuous
  have hsamples :
      (∑ m ∈ Finset.Ico y Z,
          roughSaiasNormalFormThetaWeight X (m + 1)) =
        FriableAsymptotic.integerAbelMain
          (roughSaiasNormalFormThetaWeight X) y Z := by
    rw [FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
      FriableAsymptotic.sum_Ioc_shift]
  rw [hsamples] at hcontinuous
  exact hcontinuous

/-- Exact quadrature interpretation of the integer Abel consistency term. -/
theorem roughSaiasIntegerAbelConsistencyDefect_eq_cellRemainders
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasIntegerAbelConsistencyDefect X y Z =
      ∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealBuchstabCellRemainder X m := by
  have hcells := roughSaiasNaturalMain_buchstab_sum_cells
    hy2 hyZ hZX hu5
  unfold roughSaiasIntegerAbelConsistencyDefect
  linarith





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSelectorLedgerBound -/
section


/-!
# Summing the upper-cell quotient-selector ledger

On cells above the square-root transition the fully real Buchstab
integrand is the elementary quotient selector

`floor (X / s) / log s`.

The cell ledger from `RoughSaiasFullyRealBuchstabCells` has two pieces.
The natural quotient drops telescope exactly, while the reciprocal-log
variation is bounded by the convergent `sum 1 / m^2` tail.  This file makes
that summation quantitative without any asymptotic or defect premise.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section



theorem roughSaiasNaturalQuotientDrop_nonneg
    (X : ℕ) {m : ℕ} (hm : 0 < m) :
    0 ≤ roughSaiasNaturalQuotientDrop X m := by
  unfold roughSaiasNaturalQuotientDrop
  apply sub_nonneg.mpr
  exact_mod_cast Nat.div_le_div_left (a := X) (Nat.le_succ m) hm

/-- The quotient-drop part telescopes before any estimate is taken. -/
theorem sum_roughSaiasNaturalQuotientDrop
    (X : ℕ) {M Z : ℕ} (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z, roughSaiasNaturalQuotientDrop X m) =
      ((X / M : ℕ) : ℝ) - ((X / Z : ℕ) : ℝ) := by
  induction Z, hMZ using Nat.le_induction with
  | base => simp
  | succ Z hMZ ih =>
      rw [Finset.sum_Ico_succ_top hMZ, ih]
      unfold roughSaiasNaturalQuotientDrop
      ring





theorem roughSaias_invLog_succ_sub_nonneg
    {m : ℕ} (hm2 : 2 ≤ m) :
    0 ≤ 1 / Real.log (m : ℝ) -
      1 / Real.log ((m + 1 : ℕ) : ℝ) := by
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogmono : Real.log (m : ℝ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < m by omega))
      (by exact_mod_cast (Nat.le_succ m))
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hlogm hlogmono)

/-- One reciprocal-log step costs at most
`1 / (m log(M)^2)` uniformly for `m ≥ M`. -/
theorem roughSaias_invLog_succ_sub_le
    {M m : ℕ} (hM2 : 2 ≤ M) (hMm : M ≤ m) :
    1 / Real.log (m : ℝ) -
        1 / Real.log ((m + 1 : ℕ) : ℝ) ≤
      1 / ((m : ℝ) * Real.log (M : ℝ) ^ 2) := by
  have hm2 : 2 ≤ m := hM2.trans hMm
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < M by omega)
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hm1pos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogm1 : 0 < Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega))
  have hlogMm : Real.log (M : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hMpos (by exact_mod_cast hMm)
  have hlogMm1 : Real.log (M : ℝ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) :=
    hlogMm.trans (Real.log_le_log hmpos (by exact_mod_cast (Nat.le_succ m)))
  have hgapNonneg :
      0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) :=
    sub_nonneg.mpr
      (Real.log_le_log hmpos (by exact_mod_cast (Nat.le_succ m)))
  have hgap :
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤
        1 / (m : ℝ) := by
    have hratio : 0 < ((m + 1 : ℕ) : ℝ) / (m : ℝ) :=
      div_pos hm1pos hmpos
    have h := Real.log_le_sub_one_of_pos hratio
    calc
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) =
          Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
        rw [Real.log_div hm1pos.ne' hmpos.ne']
      _ ≤ ((m + 1 : ℕ) : ℝ) / (m : ℝ) - 1 := h
      _ = 1 / (m : ℝ) := by
        field_simp [hmpos.ne']
        norm_num
  have hdenom : Real.log (M : ℝ) ^ 2 ≤
      Real.log (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ) := by
    rw [pow_two]
    exact mul_le_mul hlogMm hlogMm1 hlogM.le hlogm.le
  have hinvIdentity :
      1 / Real.log (m : ℝ) -
          1 / Real.log ((m + 1 : ℕ) : ℝ) =
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) /
          (Real.log (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ)) := by
    field_simp [hlogm.ne', hlogm1.ne']
  rw [hinvIdentity]
  calc
    (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) /
          (Real.log (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ)) ≤
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) /
          Real.log (M : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hgapNonneg (sq_pos_of_pos hlogM) hdenom
    _ ≤ (1 / (m : ℝ)) / Real.log (M : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hgap (sq_nonneg _)
    _ = 1 / ((m : ℝ) * Real.log (M : ℝ) ^ 2) := by ring

/-- A cell ledger is a telescoping quotient drop at the fixed left-hand
logarithm, plus an inverse-square summable tail. -/
theorem roughSaiasSelectorCellLedger_le_drop_add_invSq
    (X : ℕ) {M m : ℕ} (hM2 : 2 ≤ M) (hMm : M ≤ m) :
    roughSaiasSelectorCellLedger X m ≤
      roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) +
        ((X : ℝ) / Real.log (M : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) := by
  have hm2 : 2 ≤ m := hM2.trans hMm
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogMm : Real.log (M : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < M by omega))
      (by exact_mod_cast hMm)
  have hdropNonneg : 0 ≤ roughSaiasNaturalQuotientDrop X m :=
    roughSaiasNaturalQuotientDrop_nonneg X (by omega)
  have hfirst :
      roughSaiasNaturalQuotientDrop X m / Real.log (m : ℝ) ≤
        roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) :=
    div_le_div_of_nonneg_left hdropNonneg hlogM hlogMm
  have hinvNonneg := roughSaias_invLog_succ_sub_nonneg hm2
  have hinvBound := roughSaias_invLog_succ_sub_le hM2 hMm
  have hquotient : ((X / (m + 1) : ℕ) : ℝ) ≤
      (X : ℝ) / (m : ℝ) := by
    calc
      ((X / (m + 1) : ℕ) : ℝ) ≤
          (X : ℝ) / ((m + 1 : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ (X : ℝ) / (m : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hmpos
          (by exact_mod_cast (Nat.le_succ m))
  have hsecond :
      ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) ≤
        ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
          (1 / (m : ℝ) ^ 2) := by
    calc
      ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) ≤
        ((X : ℝ) / (m : ℝ)) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hquotient hinvNonneg
      _ ≤ ((X : ℝ) / (m : ℝ)) *
          (1 / ((m : ℝ) * Real.log (M : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hinvBound (by positivity)
      _ = ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
          (1 / (m : ℝ) ^ 2) := by ring
  unfold roughSaiasSelectorCellLedger
    roughSaiasNaturalQuotientDrop
  exact add_le_add hfirst hsecond

/-- Explicit sum of all upper selector ledgers. -/
theorem sum_roughSaiasSelectorCellLedger_le
    (X : ℕ) {M Z : ℕ} (hM2 : 2 ≤ M) (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z, roughSaiasSelectorCellLedger X m) ≤
      (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) +
        2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) := by
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hfirst :
      (∑ m ∈ Finset.Ico M Z,
          roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ)) ≤
        (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) := by
    calc
      (∑ m ∈ Finset.Ico M Z,
          roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ)) =
        (∑ m ∈ Finset.Ico M Z,
          roughSaiasNaturalQuotientDrop X m) / Real.log (M : ℝ) := by
            rw [Finset.sum_div]
      _ = (((X / M : ℕ) : ℝ) - ((X / Z : ℕ) : ℝ)) /
          Real.log (M : ℝ) := by
            rw [sum_roughSaiasNaturalQuotientDrop X hMZ]
      _ ≤ ((X / M : ℕ) : ℝ) / Real.log (M : ℝ) :=
        div_le_div_of_nonneg_right
          (sub_le_self _ (by positivity)) hlogM.le
      _ ≤ ((X : ℝ) / (M : ℝ)) / Real.log (M : ℝ) :=
        div_le_div_of_nonneg_right Nat.cast_div_le hlogM.le
      _ = (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) := by ring
  have hcoef : 0 ≤ (X : ℝ) / Real.log (M : ℝ) ^ 2 := by positivity
  have hsecond :
      (∑ m ∈ Finset.Ico M Z,
          ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
            (1 / (m : ℝ) ^ 2)) ≤
        2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) := by
    calc
      (∑ m ∈ Finset.Ico M Z,
          ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
            (1 / (m : ℝ) ^ 2)) =
        ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
          (∑ m ∈ Finset.Ico M Z, 1 / (m : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
      _ ≤ ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
          (2 / (M : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (FriableAsymptotic.sum_Ico_inv_sq_le (show 1 ≤ M by omega))
          hcoef
      _ = 2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) := by ring
  calc
    (∑ m ∈ Finset.Ico M Z, roughSaiasSelectorCellLedger X m) ≤
      ∑ m ∈ Finset.Ico M Z,
        (roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) +
          ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
            (1 / (m : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro m hm
        exact roughSaiasSelectorCellLedger_le_drop_add_invSq X hM2
          (Finset.mem_Ico.mp hm).1
    _ = (∑ m ∈ Finset.Ico M Z,
          roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ)) +
        ∑ m ∈ Finset.Ico M Z,
          ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
            (1 / (m : ℝ) ^ 2) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) +
        2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) :=
      add_le_add hfirst hsecond

/-- The complete upper-cell remainder block has the explicit elementary
bound obtained by summing its selector ledgers. -/
theorem abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_explicit
    {X M Z : ℕ} (hX : 0 < X) (hM2 : 2 ≤ M)
    (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) +
        2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) := by
  exact (abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_selectorLedger
    hX hM2 hupper).trans
      (sum_roughSaiasSelectorCellLedger_le X hM2 hMZ)

/-- At the square-root transition or above, the upper-cell block is already
of inverse-log-square size (with a deliberately coarse constant `3`). -/
theorem abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_three_invLogSq
    {X M Z : ℕ} (hX : 0 < X) (hM2 : 2 ≤ M)
    (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      3 * (X : ℝ) / Real.log (M : ℝ) ^ 2 := by
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (show 1 ≤ M by omega)
  have hlogMleM : Real.log (M : ℝ) ≤ (M : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (by exact_mod_cast (show 0 < M by omega) : (0 : ℝ) < (M : ℝ))
    linarith
  have hdenomOne : Real.log (M : ℝ) ^ 2 ≤
      (M : ℝ) * Real.log (M : ℝ) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hlogMleM hlogM.le
  have hdenomTwo : Real.log (M : ℝ) ^ 2 ≤
      (M : ℝ) * Real.log (M : ℝ) ^ 2 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hMone (sq_nonneg (Real.log (M : ℝ)))
  have hfirst :
      (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) ≤
        (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlogM) hdenomOne
  have hsecond :
      2 * (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ) ^ 2) ≤
        2 * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlogM) hdenomTwo
  calc
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) +
        2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) :=
      abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_explicit
        hX hM2 hMZ hupper
    _ ≤ (X : ℝ) / Real.log (M : ℝ) ^ 2 +
        2 * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
      add_le_add hfirst hsecond
    _ = 3 * (X : ℝ) / Real.log (M : ℝ) ^ 2 := by ring



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasFullyRealNaturalCells -/
section


/-!
# Fully real cells with the floor/frac-paired natural endpoint sample

Sampling a fully real Buchstab cell by the continuous real-quotient theta
weight leaves a separate signed floor correction.  Sampling instead by the
natural quotient theta weight pairs that correction inside the cell.  The
sum of these paired cells is therefore exactly the natural integer Abel
consistency defect, with no signed-floor term left over.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section



/-- Exact pointwise pairing of the continuous cell remainder and the signed
fractional endpoint correction. -/
theorem roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_continuous_add_fractional
    (X m : ℕ) :
    roughSaiasFullyRealNaturalBuchstabCellRemainder X m =
      roughSaiasFullyRealBuchstabCellRemainder X m +
        roughSaiasFractionalCorrectionThetaWeight X (m + 1) := by
  rfl



/-- The paired natural endpoint sample is also the elementary quotient
selector on every upper cell. -/
theorem roughSaiasNaturalQuotientThetaWeight_eq_selector_of_sq_le
    {X m : ℕ} (hm2 : 2 ≤ m) (hupper : X ≤ m ^ 2) :
    roughSaiasNaturalQuotientThetaWeight X (m + 1) =
      roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ) := by
  have hmpos : 0 < m := by omega
  have hquotientLe : X / (m + 1) ≤ m := by
    calc
      X / (m + 1) ≤ X / m :=
        Nat.div_le_div_left (a := X) (Nat.le_succ m) hmpos
      _ ≤ m ^ 2 / m := Nat.div_le_div_right hupper
      _ = m := by
        simpa only [pow_two] using Nat.mul_div_left m hmpos
  unfold roughSaiasNaturalQuotientThetaWeight
    roughSaiasRealQuotientSelectorIntegrand
  rw [Nat.floor_div_eq_div]
  congr 1
  unfold roughSaiasNaturalMain
  by_cases hquotientZero : X / (m + 1) = 0
  · simp [hquotientZero]
  · have hquotientPos : 0 < X / (m + 1) := Nat.pos_of_ne_zero hquotientZero
    have hcoord := FriableAsymptotic.dickmanU_le_one hquotientPos
      (show 1 < m + 1 by omega) (hquotientLe.trans (Nat.le_succ m))
    rw [roughSaiasG_eq_one_of_le_one hcoord, mul_one]

/-- Consequently, on an upper cell the paired natural remainder is exactly
the already bounded selector remainder. -/
theorem roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_selectorRemainder
    {X m : ℕ} (hX : 0 < X) (hm2 : 2 ≤ m) (hupper : X ≤ m ^ 2) :
    roughSaiasFullyRealNaturalBuchstabCellRemainder X m =
      roughSaiasFullyRealBuchstabCellRemainder X m := by
  have hcontinuous :=
    roughSaiasNormalFormThetaWeight_eq_selector_of_sq_le hX hm2 hupper
  have hnatural :=
    roughSaiasNaturalQuotientThetaWeight_eq_selector_of_sq_le hm2 hupper
  have hpair :=
    roughSaiasNormalFormThetaWeight_eq_natural_add_fractional X (m + 1)
  rw [hcontinuous, hnatural] at hpair
  have hfractional :
      roughSaiasFractionalCorrectionThetaWeight X (m + 1) = 0 := by
    linarith
  rw [roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_continuous_add_fractional,
    hfractional, add_zero]

/-- The natural integer Abel consistency defect is exactly the sum of the
floor/frac-paired fully real cell remainders. -/
theorem roughSaiasNaturalIntegerAbelConsistencyDefect_eq_naturalCellRemainders
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalIntegerAbelConsistencyDefect X y Z =
      ∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m := by
  have hcontinuous :=
    roughSaiasIntegerAbelConsistencyDefect_eq_cellRemainders
      hy2 hyZ hZX hu5
  have habel :=
    roughSaiasIntegerAbelMain_normalForm_eq_natural_add_fractional
      (X := X) hyZ
  have hfractional :
      FriableAsymptotic.integerAbelMain
          (roughSaiasFractionalCorrectionThetaWeight X) y Z =
        ∑ m ∈ Finset.Ico y Z,
          roughSaiasFractionalCorrectionThetaWeight X (m + 1) := by
    rw [FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
      FriableAsymptotic.sum_Ioc_shift]
  have hcells :
      (∑ m ∈ Finset.Ico y Z,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m) =
        (∑ m ∈ Finset.Ico y Z,
          roughSaiasFullyRealBuchstabCellRemainder X m) +
        ∑ m ∈ Finset.Ico y Z,
          roughSaiasFractionalCorrectionThetaWeight X (m + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _hm
    exact
      roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_continuous_add_fractional
        X m
  calc
    roughSaiasNaturalIntegerAbelConsistencyDefect X y Z =
        roughSaiasIntegerAbelConsistencyDefect X y Z +
          FriableAsymptotic.integerAbelMain
            (roughSaiasFractionalCorrectionThetaWeight X) y Z := by
      unfold roughSaiasNaturalIntegerAbelConsistencyDefect
        roughSaiasIntegerAbelConsistencyDefect
      rw [habel]
      ring
    _ = (∑ m ∈ Finset.Ico y Z,
          roughSaiasFullyRealBuchstabCellRemainder X m) +
        ∑ m ∈ Finset.Ico y Z,
          roughSaiasFractionalCorrectionThetaWeight X (m + 1) := by
      rw [hcontinuous, hfractional]
    _ = ∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m := hcells.symm

/-- Exact master identity with both the natural-base discrepancy and the
signed quotient floors absorbed into paired fully real unit cells. -/
theorem roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_naturalTheta
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
      roughSaiasNaturalThetaErrorTransfer X y Z := by
  rw [roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta,
    roughSaiasNaturalIntegerAbelConsistencyDefect_eq_naturalCellRemainders
      hy2 hyZ hZX hu5]





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasNaturalThetaLedgerBound -/
section


/-!
# Deterministic reduction of the natural-theta transfer ledger

The fourth-power PNT input is already unconditional in the project.  This
file bounds both endpoint coefficients in its finite-Abel ledger and leaves
only one explicit weighted discrete variation of the paired natural theta
weight.  Thus neither a defect bound nor a signed-floor estimate remains as
an input to the theta transfer.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section





/-- Uniform size bound for the paired natural theta weight throughout the
compact Buchstab interval. -/
theorem roughSaiasNaturalQuotientThetaWeight_abs_le_sixteen
    {X y Z m : ℕ} (hy2 : 2 ≤ y) (_hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hm : m ∈ Finset.Ioc y Z) :
    |roughSaiasNaturalQuotientThetaWeight X m| ≤
      16 * (X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) := by
  have hmData := Finset.mem_Ioc.mp hm
  have hm2 : 2 ≤ m := by omega
  have hmposNat : 0 < m := by omega
  have hmX : m ≤ X := hmData.2.trans hZX
  have hquotientPos : 0 < X / m := Nat.div_pos hmX hmposNat
  have hquotientOne : 1 ≤ X / m := hquotientPos
  have hquotientX : X / m ≤ X := Nat.div_le_self X m
  have hypos : 0 < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmposNat
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hquotientPosR : 0 < ((X / m : ℕ) : ℝ) := by
    exact_mod_cast hquotientPos
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogq0 : 0 ≤ Real.log ((X / m : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hquotientOne)
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogqX : Real.log ((X / m : ℕ) : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hquotientPosR (by exact_mod_cast hquotientX)
  have hlogym : Real.log (y : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hypos (by exact_mod_cast hmData.1.le)
  have hcoord0 :
      0 ≤ Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) :=
    div_nonneg hlogq0 hlogm.le
  have hcoord5 :
      Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5 := by
    calc
      Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤
          Real.log (X : ℝ) / Real.log (m : ℝ) :=
        div_le_div_of_nonneg_right hlogqX hlogm.le
      _ ≤ Real.log (X : ℝ) / Real.log (y : ℝ) :=
        div_le_div_of_nonneg_left hlogX0 hlogy hlogym
      _ ≤ 5 := hu5
  have hG :
      |roughSaiasG m
          (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))| ≤ 16 := by
    rw [← roughSaiasFullyRealG_nat]
    exact roughSaiasFullyRealG_abs_le_sixteen
      (by exact_mod_cast (show 1 < m by omega)) ⟨hcoord0, hcoord5⟩
  have hquotientReal : ((X / m : ℕ) : ℝ) ≤
      (X : ℝ) / (m : ℝ) := Nat.cast_div_le
  unfold roughSaiasNaturalQuotientThetaWeight roughSaiasNaturalMain
    FriableAsymptotic.dickmanU
  rw [abs_div, abs_mul, abs_of_nonneg (by positivity), abs_of_pos hlogm]
  calc
    ((X / m : ℕ) : ℝ) *
          |roughSaiasG m
            (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))| /
        Real.log (m : ℝ) ≤
      (((X : ℝ) / (m : ℝ)) * 16) / Real.log (m : ℝ) := by
        apply div_le_div_of_nonneg_right _ hlogm.le
        exact mul_le_mul hquotientReal hG (abs_nonneg _) (by positivity)
    _ = 16 * (X : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) := by
      ring

/-- Both endpoint terms in the natural-theta PNT ledger are now explicit;
only its interior weighted variation remains. -/
theorem roughSaiasNaturalThetaPNTLedger_le_endpoint_add_variation
    {A C : ℝ} {X y Z : ℕ} (hC : 0 ≤ C)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalThetaPNTLedger A C X y Z ≤
      roughSaiasNaturalThetaPNTEndpointEnvelope A C X y Z +
        roughSaiasNaturalThetaPNTVariationLedger A C X y Z := by
  have hZmem : Z ∈ Finset.Ioc y Z := Finset.mem_Ioc.mpr ⟨hyZ, le_rfl⟩
  have hy1mem : y + 1 ∈ Finset.Ioc y Z :=
    Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  have hZend := roughSaiasNaturalQuotientThetaWeight_abs_le_sixteen
    hy2 hyZ hZX hu5 hZmem
  have hyend := roughSaiasNaturalQuotientThetaWeight_abs_le_sixteen
    hy2 hyZ hZX hu5 hy1mem
  have hZfactor : 0 ≤
      C * ((Z : ℝ) / Real.log (Z : ℝ) ^ A) := by positivity
  have hyfactor : 0 ≤
      C * ((y : ℝ) / Real.log (y : ℝ) ^ A) := by positivity
  unfold roughSaiasNaturalThetaPNTLedger
    roughSaiasNaturalThetaPNTEndpointEnvelope
    roughSaiasNaturalThetaPNTVariationLedger
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_right hZend hZfactor)
      (mul_le_mul_of_nonneg_right hyend hyfactor))
    le_rfl

/-- At fourth-power PNT strength the two endpoint terms have an additional
full reciprocal logarithm. -/
theorem roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le
    {C : ℝ} {X y Z : ℕ} (hC : 0 ≤ C) (hy2 : 2 ≤ y) (hyZ : y < Z) :
    roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ) C X y Z ≤
      32 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 := by
  have hypos : 0 < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hy1pos : 0 < ((y + 1 : ℕ) : ℝ) := by positivity
  have hZpos : 0 < (Z : ℝ) := by
    exact_mod_cast (show 0 < Z by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogy1 : 0 < Real.log ((y + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y + 1 by omega))
  have hlogZ : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hlogyZ : Real.log (y : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log hypos (by exact_mod_cast hyZ.le)
  have hlogyy1 : Real.log (y : ℝ) ≤
      Real.log ((y + 1 : ℕ) : ℝ) :=
    Real.log_le_log hypos (by exact_mod_cast (Nat.le_succ y))
  have hnumerator : 0 ≤ 16 * C * (X : ℝ) := by positivity
  have hZpow : Real.log (y : ℝ) ^ 5 ≤ Real.log (Z : ℝ) ^ 5 :=
    pow_le_pow_left₀ hlogy.le hlogyZ 5
  have hZterm :
      (16 * (X : ℝ) / ((Z : ℝ) * Real.log (Z : ℝ))) *
          (C * ((Z : ℝ) / Real.log (Z : ℝ) ^ 4)) ≤
        16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 := by
    calc
      (16 * (X : ℝ) / ((Z : ℝ) * Real.log (Z : ℝ))) *
          (C * ((Z : ℝ) / Real.log (Z : ℝ) ^ 4)) =
        16 * C * (X : ℝ) / Real.log (Z : ℝ) ^ 5 := by
          field_simp [hZpos.ne', hlogZ.ne']
      _ ≤ 16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 :=
        div_le_div_of_nonneg_left hnumerator (pow_pos hlogy 5) hZpow
  have hyDenom :
      (y : ℝ) * Real.log (y : ℝ) ≤
        ((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ) := by
    exact mul_le_mul (by exact_mod_cast (Nat.le_succ y)) hlogyy1
      hlogy.le (by positivity)
  have hyWeight :
      16 * (X : ℝ) /
          (((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ)) ≤
        16 * (X : ℝ) / ((y : ℝ) * Real.log (y : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity)
      (mul_pos hypos hlogy) hyDenom
  have hyFactor : 0 ≤ C * ((y : ℝ) / Real.log (y : ℝ) ^ 4) := by
    positivity
  have hyTerm :
      (16 * (X : ℝ) /
          (((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ))) *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ 4)) ≤
        16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 := by
    calc
      (16 * (X : ℝ) /
          (((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ))) *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ 4)) ≤
        (16 * (X : ℝ) / ((y : ℝ) * Real.log (y : ℝ))) *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_right hyWeight hyFactor
      _ = 16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 := by
        field_simp [hypos.ne', hlogy.ne']
  unfold roughSaiasNaturalThetaPNTEndpointEnvelope
  have hZpowFour : Real.log (Z : ℝ) ^ (4 : ℝ) =
      Real.log (Z : ℝ) ^ (4 : ℕ) := by
    simpa only [Nat.cast_ofNat] using
      Real.rpow_natCast (Real.log (Z : ℝ)) 4
  have hypowFour : Real.log (y : ℝ) ^ (4 : ℝ) =
      Real.log (y : ℝ) ^ (4 : ℕ) := by
    simpa only [Nat.cast_ofNat] using
      Real.rpow_natCast (Real.log (y : ℝ)) 4
  rw [hZpowFour, hypowFour]
  calc
    (16 * (X : ℝ) / ((Z : ℝ) * Real.log (Z : ℝ))) *
          (C * ((Z : ℝ) / Real.log (Z : ℝ) ^ 4)) +
        (16 * (X : ℝ) /
          (((y + 1 : ℕ) : ℝ) * Real.log ((y + 1 : ℕ) : ℝ))) *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ 4)) ≤
      16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 +
        16 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 :=
      add_le_add hZterm hyTerm
    _ = 32 * C * (X : ℝ) / Real.log (y : ℝ) ^ 5 := by ring

/-- For `y ≥ 3`, the endpoint envelope is already of the target
inverse-log-square size. -/
theorem roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le_invLogSq
    {C : ℝ} {X y Z : ℕ} (hC : 0 ≤ C) (hy3 : 3 ≤ y) (hyZ : y < Z) :
    roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ) C X y Z ≤
      32 * C * (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  have hypos : 0 < (y : ℝ) := by positivity
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogyOne : 1 ≤ Real.log (y : ℝ) := by
    have hexp : Real.exp 1 < (y : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hy3)
    exact ((Real.lt_log_iff_exp_lt hypos).2 hexp).le
  have honeCube : 1 ≤ Real.log (y : ℝ) ^ 3 := one_le_pow₀ hlogyOne
  have hpowers : Real.log (y : ℝ) ^ 2 ≤ Real.log (y : ℝ) ^ 5 := by
    calc
      Real.log (y : ℝ) ^ 2 = Real.log (y : ℝ) ^ 2 * 1 := by ring
      _ ≤ Real.log (y : ℝ) ^ 2 * Real.log (y : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left honeCube (sq_nonneg _)
      _ = Real.log (y : ℝ) ^ 5 := by ring
  have hnumerator : 0 ≤ 32 * C * (X : ℝ) := by positivity
  exact (roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le
    hC (by omega) hyZ).trans
      (div_le_div_of_nonneg_left hnumerator (pow_pos hlogy 2) hpowers)

/-- General PNT-to-theta transfer with the endpoint estimates already
discharged. -/
theorem roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation
    {A C : ℝ} {X₀ X y Z : ℕ}
    (htheta : ∀ T, X₀ ≤ T →
      |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ A))
    (hC : 0 ≤ C) (hX₀y : X₀ ≤ y)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      roughSaiasNaturalThetaPNTEndpointEnvelope A C X y Z +
        roughSaiasNaturalThetaPNTVariationLedger A C X y Z := by
  exact (roughSaiasNaturalThetaErrorTransfer_abs_le_pntLedger
    htheta hX₀y hyZ).trans
      (roughSaiasNaturalThetaPNTLedger_le_endpoint_add_variation
        hC hy2 hyZ hZX hu5)

/-- Closed fourth-power specialization.  No analytic premise remains; the
only unestimated object is the explicit deterministic weight variation. -/
theorem roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation_fourthPower
    {X y Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z +
        roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z := by
  exact roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation
    roughSaiasThetaFourthPower_bound
      roughSaiasThetaFourthPowerConstant_pos.le hY
        hy2 hyZ hZX hu5



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasCellTransitionSplit -/
section


/-!
# Splitting at the square-root selector transition

The upper selector cells and the Dickman core of the theta transfer are
already of inverse-log-square size.  This file records the exact split at
an arbitrary transition `M`.  It isolates precisely two remaining explicit
terms: the lower paired-cell block and the natural-minus-Dickman theta
residual.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



theorem le_roughSaiasSelectorTransition (X y : ℕ) :
    y ≤ roughSaiasSelectorTransition X y := by
  exact le_max_left _ _

theorem roughSaiasSelectorTransition_sq_ge (X y : ℕ) :
    X ≤ roughSaiasSelectorTransition X y ^ 2 := by
  have hsqrt : X < (Nat.sqrt X + 1) ^ 2 := Nat.lt_succ_sqrt' X
  have htransition : Nat.sqrt X + 1 ≤ roughSaiasSelectorTransition X y := by
    exact le_max_right _ _
  exact (Nat.le_of_lt hsqrt).trans (Nat.pow_le_pow_left htransition 2)

theorem roughSaiasSelectorTransition_le
    {X y : ℕ} (hX2 : 2 ≤ X) (hyX : y ≤ X) :
    roughSaiasSelectorTransition X y ≤ X := by
  unfold roughSaiasSelectorTransition
  apply max_le hyX
  have hsqrt : Nat.sqrt X < X := Nat.sqrt_lt_self (by omega)
  omega

/-- Exact adjacent split of the paired fully real cell sum. -/
theorem sum_roughSaiasFullyRealNaturalCells_split
    (X : ℕ) {y M Z : ℕ} (hyM : y ≤ M) (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) =
      (∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) +
      ∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m := by
  rw [← Finset.sum_Ico_consecutive _ hyM hMZ]

/-- The natural integer consistency defect split into lower cells and the
upper selector block. -/
theorem roughSaiasNaturalIntegerAbelConsistencyDefect_eq_splitCells
    {X y M Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hyM : y ≤ M) (hMZ : M ≤ Z) :
    roughSaiasNaturalIntegerAbelConsistencyDefect X y Z =
      (∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) +
      ∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m := by
  rw [roughSaiasNaturalIntegerAbelConsistencyDefect_eq_naturalCellRemainders
    hy2 hyZ hZX hu5,
    sum_roughSaiasFullyRealNaturalCells_split X hyM hMZ]

/-- Above any transition satisfying `X ≤ M²`, the paired natural cells
inherit the closed selector bound. -/
theorem abs_sum_roughSaiasFullyRealNaturalCells_upper_le_three_invLogSq
    {X M Z : ℕ} (hX : 0 < X) (hM2 : 2 ≤ M)
    (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
      3 * (X : ℝ) / Real.log (M : ℝ) ^ 2 := by
  have hsum :
      (∑ m ∈ Finset.Ico M Z,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m) =
        ∑ m ∈ Finset.Ico M Z,
          roughSaiasFullyRealBuchstabCellRemainder X m := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := hM2.trans hmData.1
    have hMmSq : M ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hmData.1 2
    exact roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_selectorRemainder
      hX hm2 (hupper.trans hMmSq)
  rw [hsum]
  exact abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_three_invLogSq
    hX hM2 hMZ hupper

/-- Quantitative transition split: the entire upper block is charged at
the original left-endpoint logarithm, so only the lower-cell sum remains. -/
theorem roughSaiasNaturalIntegerAbelConsistencyDefect_abs_le_lowerCells_add_three
    {X y M Z : ℕ} (hX : 0 < X) (hy2 : 2 ≤ y) (hyZ : y < Z)
    (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hyM : y ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| ≤
      |∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
      3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  have hM2 : 2 ≤ M := hy2.trans hyM
  have hupperBound :=
    abs_sum_roughSaiasFullyRealNaturalCells_upper_le_three_invLogSq
      hX hM2 hMZ hupper
  have hypos : 0 < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogyM : Real.log (y : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log hypos (by exact_mod_cast hyM)
  have hpowers : Real.log (y : ℝ) ^ 2 ≤ Real.log (M : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlogy.le hlogyM 2
  have hupperAtY :
      |∑ m ∈ Finset.Ico M Z,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
        3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
    hupperBound.trans
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlogy) hpowers)
  rw [roughSaiasNaturalIntegerAbelConsistencyDefect_eq_splitCells
    hy2 hyZ hZX hu5 hyM hMZ]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hupperAtY)





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasQuotientBlocks -/
section


/-!
# Hyperbola blocks for the Saias base variation

The transformed sawtooth kernel has a fixed natural quotient on each fibre
of `m ↦ X / m`.  This file records the elementary, but useful, fact that
those fibres are honest intervals and gives a fibrewise decomposition of
finite sums.  No estimate is used here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section























/-! ## The dual hyperbola partition -/

























/-! ## Adjacent edges: stable quotient fibres and quotient jumps -/





































/-- After the weighted boundary telescope is inserted in the full finite
Abel formula, both global endpoint products and the stable-edge sum cancel.
The entire natural theta transfer is therefore exactly one signed local
prime-minus-integer residual. -/
theorem roughSaiasNaturalThetaErrorTransfer_eq_localPrimeErrorResidual
    {X y Z : ℕ} (hyZ : y < Z) :
    roughSaiasNaturalThetaErrorTransfer X y Z =
      ∑ m ∈ Finset.Ioc y Z,
        roughSaiasNaturalQuotientThetaWeight X m *
          (FriableAsymptotic.primeLogIncrement m - 1) := by
  unfold roughSaiasNaturalThetaErrorTransfer
  rw [FriableAsymptotic.primeThetaWeightedInterval_eq_Ioc,
    FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  ring

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpCorrectionTarget -/
section


/-!
# The sharp fully real correction target

The reverse defect splits directly into:

1. the ordinary Dickman continuous-integral versus prime-theta
   discrepancy, already closed by the existing Riemann and fourth-power
   PNT estimates; and
2. one fully real Saias correction integral versus its matching residual
   prime weight.

This is the minimal analytic target left after all exact base changes,
floor pairings, upper-selector cells, and standard Dickman estimates have
been discharged.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section





















/-- Fully local form of the reverse defect after weighted boundary
cancellation.  All finite-Abel endpoints, stable quotient blocks, and jump
boundaries have cancelled; what remains is the signed pairing of the natural
cell remainders with one local prime-minus-integer mass sum. -/
theorem roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_localPrimeErrorResidual
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
      ∑ m ∈ Finset.Ioc y Z,
        roughSaiasNaturalQuotientThetaWeight X m *
          (FriableAsymptotic.primeLogIncrement m - 1) := by
  rw [roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_naturalTheta
      hy2 hyZ hZX hu5,
    roughSaiasNaturalThetaErrorTransfer_eq_localPrimeErrorResidual hyZ]

/-- Cellwise form of the preceding identity.  The natural-cell remainder
and local prime mass are paired before either absolute value is taken. -/
theorem roughSaiasReverseNormalFormDefect_eq_sum_localNaturalPrimeCellDiscrepancy
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      ∑ m ∈ Finset.Ico y Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m := by
  rw [roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_localPrimeErrorResidual
      hy2 hyZ hZX hu5,
    FriableAsymptotic.sum_Ioc_shift, ← Finset.sum_sub_distrib]
  rfl

/-- Exact adjacent split of the fully paired local discrepancy. -/
theorem sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_split
    (X : ℕ) {y M Z : ℕ} (hyM : y ≤ M) (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico y Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m) =
      (∑ m ∈ Finset.Ico y M,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m) +
      ∑ m ∈ Finset.Ico M Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m := by
  rw [← Finset.sum_Ico_consecutive _ hyM hMZ]









/-! ## Closing the lower fully-real quadrature -/





























/-- The fourth-power PNT variation ledger is controlled on every compact
Saias face, with no square-root or selector assumption. -/
theorem roughSaiasNaturalThetaPNTVariationLedger_fourth_le_invLogSq
    {C : ℝ} (hC : 0 ≤ C) {X y Z : ℕ}
    (hy3 : 3 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ) C X y Z ≤
      211 * C * (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  have hedgeSubset : Finset.Ioc y (Z - 1) ⊆ Finset.Ico y Z := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    rw [Finset.mem_Ico]
    omega
  have hnonneg : ∀ m ∈ Finset.Ico y Z,
      0 ≤ |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
        (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hlogm : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    exact mul_nonneg (abs_nonneg _) (by positivity)
  unfold roughSaiasNaturalThetaPNTVariationLedger
  rw [← Nat.cast_ofNat (n := 4)]
  simp_rw [Real.rpow_natCast]
  calc
    (∑ m ∈ Finset.Ioc y (Z - 1),
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      ∑ m ∈ Finset.Ico y Z,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hedgeSubset
        (fun m hm _hnot => hnonneg m hm)
    _ ≤ 211 * C * (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
      sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq
        hC hy3 hyZ hZX hu5





/-- The full natural-theta prime-minus-integer transfer is closed on the
upper selector face. -/
theorem roughSaiasNaturalThetaErrorTransfer_abs_le_upper_invLogSq
    {X M Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ M)
    (hM3 : 3 ≤ M) (hMZ : M < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (M : ℝ) ≤ 5)
    (hupper : X ≤ M ^ 2) :
    |roughSaiasNaturalThetaErrorTransfer X M Z| ≤
      45 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (M : ℝ) ^ 2 := by
  have htransfer :=
    roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation_fourthPower
      hY (by omega) hMZ hZX hu5
  have hendpoint :=
    roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le_invLogSq
      (C := roughSaiasThetaFourthPowerConstant) (X := X)
      roughSaiasThetaFourthPowerConstant_pos.le hM3 hMZ
  have hvariation :=
    roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq
      roughSaiasThetaFourthPowerConstant_pos.le hM3 hMZ.le hZX hu5 hupper
  calc
    |roughSaiasNaturalThetaErrorTransfer X M Z| ≤
      roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X M Z +
        roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X M Z := htransfer
    _ ≤ 32 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
          Real.log (M : ℝ) ^ 2 +
        13 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
          Real.log (M : ℝ) ^ 2 :=
      add_le_add hendpoint hvariation
    _ = 45 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (M : ℝ) ^ 2 := by ring

/-- The full natural-theta prime-minus-integer transfer is closed on every
compact Saias face.  No square-root or upper-selector condition remains. -/
theorem roughSaiasNaturalThetaErrorTransfer_abs_le_invLogSq
    {X y Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      243 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have htransfer :=
    roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation_fourthPower
      hY (by omega) hyZ hZX hu5
  have hendpoint :=
    roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le_invLogSq
      (C := roughSaiasThetaFourthPowerConstant) (X := X)
      roughSaiasThetaFourthPowerConstant_pos.le hy3 hyZ
  have hvariation :=
    roughSaiasNaturalThetaPNTVariationLedger_fourth_le_invLogSq
      roughSaiasThetaFourthPowerConstant_pos.le hy3 hyZ.le hZX hu5
  calc
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z +
        roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z := htransfer
    _ ≤ 32 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        211 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 :=
      add_le_add hendpoint hvariation
    _ = 243 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by ring

/-- After the global fourth-PNT transfer is closed, the exact remaining
analytic residual is only the lower fully-real natural-cell block. -/
theorem roughSaiasReverseNormalFormDefect_abs_le_lowerNaturalCells_add_invLogSq
    {X y M Z : ℕ} (hX : 0 < X)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hyM : y ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      |∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
      (3 + 243 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have hnatural :=
    roughSaiasNaturalIntegerAbelConsistencyDefect_abs_le_lowerCells_add_three
      hX (by omega) hyZ hZX hu5 hyM hMZ hupper
  have htheta :=
    roughSaiasNaturalThetaErrorTransfer_abs_le_invLogSq
      hY hy3 hyZ hZX hu5
  rw [roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta]
  calc
    |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z -
        roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| +
        |roughSaiasNaturalThetaErrorTransfer X y Z| := abs_sub _ _
    _ ≤
      (|∑ m ∈ Finset.Ico y M,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
        3 * (X : ℝ) / Real.log (y : ℝ) ^ 2) +
      243 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 :=
      add_le_add hnatural htheta
    _ = |∑ m ∈ Finset.Ico y M,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
        (3 + 243 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 := by ring



/-- The whole paired local discrepancy above a square-root transition has
the target inverse-log-square size. -/
theorem abs_sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_upper_le_invLogSq
    {X M Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ M)
    (hM3 : 3 ≤ M) (hMZ : M ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (M : ℝ) ≤ 5)
    (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m| ≤
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (M : ℝ) ^ 2 := by
  rcases hMZ.eq_or_lt with rfl | hMZlt
  · simp only [Finset.Ico_self, Finset.sum_empty, abs_zero]
    exact div_nonneg
      (mul_nonneg
        (add_nonneg (by norm_num)
          (mul_nonneg (by norm_num)
            roughSaiasThetaFourthPowerConstant_pos.le))
        (by positivity))
      (sq_nonneg _)
  · have hXpos : 0 < X := by omega
    have hM2 : 2 ≤ M := by omega
    have hcells :=
      abs_sum_roughSaiasFullyRealNaturalCells_upper_le_three_invLogSq
        hXpos hM2 hMZlt.le hupper
    have htheta :=
      roughSaiasNaturalThetaErrorTransfer_abs_le_upper_invLogSq
        hY hM3 hMZlt hZX hu5 hupper
    calc
      |∑ m ∈ Finset.Ico M Z,
          roughSaiasLocalNaturalPrimeCellDiscrepancy X m| =
        |(∑ m ∈ Finset.Ico M Z,
            roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
          roughSaiasNaturalThetaErrorTransfer X M Z| := by
        exact congrArg (fun t : ℝ => |t|)
          ((roughSaiasReverseNormalFormDefect_eq_sum_localNaturalPrimeCellDiscrepancy
              hM2 hMZlt hZX hu5).symm.trans
            (roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_naturalTheta
              hM2 hMZlt hZX hu5))
      _ ≤ |∑ m ∈ Finset.Ico M Z,
            roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
          |roughSaiasNaturalThetaErrorTransfer X M Z| := abs_sub _ _
      _ ≤ 3 * (X : ℝ) / Real.log (M : ℝ) ^ 2 +
          45 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
            Real.log (M : ℝ) ^ 2 := add_le_add hcells htheta
      _ = (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (M : ℝ) ^ 2 := by ring

/-- Sharp reduction after closing the complete upper selector block.  Only
the signed local pairing below the square-root transition remains. -/
theorem roughSaiasReverseNormalFormDefect_abs_le_lowerLocal_add_upperInvLogSq
    {X y M Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hyM : y ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      |∑ m ∈ Finset.Ico y M,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m| +
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have hy2 : 2 ≤ y := by omega
  have hypos : 0 < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogyM : Real.log (y : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log hypos (by exact_mod_cast hyM)
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hu5M : Real.log (X : ℝ) / Real.log (M : ℝ) ≤ 5 :=
    (div_le_div_of_nonneg_left hlogX0 hlogy hlogyM).trans hu5
  have hupperBound :=
    abs_sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_upper_le_invLogSq
      (hY.trans hyM) (hy3.trans hyM) hMZ hZX hu5M hupper
  have hpowers : Real.log (y : ℝ) ^ 2 ≤ Real.log (M : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlogy.le hlogyM 2
  have hcoeffNonneg :
      0 ≤ (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) :=
    mul_nonneg
      (add_nonneg (by norm_num)
        (mul_nonneg (by norm_num)
          roughSaiasThetaFourthPowerConstant_pos.le))
      (by positivity)
  have hupperAtY :
      |∑ m ∈ Finset.Ico M Z,
          roughSaiasLocalNaturalPrimeCellDiscrepancy X m| ≤
        (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 :=
    hupperBound.trans
      (div_le_div_of_nonneg_left hcoeffNonneg (pow_pos hlogy 2) hpowers)
  rw [roughSaiasReverseNormalFormDefect_eq_sum_localNaturalPrimeCellDiscrepancy
      hy2 hyZ hZX hu5,
    sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_split X hyM hMZ]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hupperAtY)

/-- Canonical square-root-transition version of the preceding reduction. -/
theorem roughSaiasReverseNormalFormDefect_self_abs_le_canonicalLowerLocal_add_upperInvLogSq
    {X y : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      |∑ m ∈ Finset.Ico y (roughSaiasSelectorTransition X y),
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m| +
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have hX2 : 2 ≤ X := by omega
  exact
    roughSaiasReverseNormalFormDefect_abs_le_lowerLocal_add_upperInvLogSq
      hY hy3 hyX le_rfl hu5
        (le_roughSaiasSelectorTransition X y)
        (roughSaiasSelectorTransition_le hX2 hyX.le)
        (roughSaiasSelectorTransition_sq_ge X y)

/-- If the original endpoint is already above the square-root transition,
the lower residual is empty and the upper estimate closes the whole
defect. -/
theorem roughSaiasReverseNormalFormDefect_self_abs_le_upperInvLogSq_of_sqrt_succ_le
    {X y : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hsqrt : Nat.sqrt X + 1 ≤ y) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have htransition : roughSaiasSelectorTransition X y = y := by
    simp only [roughSaiasSelectorTransition, max_eq_left hsqrt]
  simpa only [htransition, Finset.Ico_self, Finset.sum_empty, abs_zero,
    zero_add] using
      (roughSaiasReverseNormalFormDefect_self_abs_le_canonicalLowerLocal_add_upperInvLogSq
        hY hy3 hyX hu5)







/-! ## Closed sharp defect and endpoint witnesses -/





/-- The reverse normal-form defect at its natural endpoint has the sharp
inverse-log-square size throughout the compact face `log X / log y ≤ 5`.
The proof splits at the square-root transition: the upper case was already
closed, while the lower case is exactly the fully-real natural-cell
quadrature proved above. -/
theorem roughSaiasReverseNormalFormDefect_self_abs_le_sharp_invLogSq
    {X y : ℕ} (hY : roughSaiasSharpDefectCutoff ≤ y)
    (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      roughSaiasSharpDefectConstant * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  have hy3 : 3 ≤ y := by
    exact (le_max_left 3 roughSaiasThetaFourthPowerCutoff).trans hY
  have hYtheta : roughSaiasThetaFourthPowerCutoff ≤ y := by
    exact (le_max_right 3 roughSaiasThetaFourthPowerCutoff).trans hY
  have hXpos : 0 < X := by omega
  have hX2 : 2 ≤ X := by omega
  have hCtheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
    roughSaiasThetaFourthPowerConstant_pos.le
  have htargetNonneg :
      0 ≤ (X : ℝ) / Real.log (y : ℝ) ^ 2 := by positivity
  by_cases hsqrt : Nat.sqrt X + 1 ≤ y
  · have hupper :=
      roughSaiasReverseNormalFormDefect_self_abs_le_upperInvLogSq_of_sqrt_succ_le
        hYtheta hy3 hyX hu5 hsqrt
    have hconst :
        3 + 45 * roughSaiasThetaFourthPowerConstant ≤
          roughSaiasSharpDefectConstant := by
      unfold roughSaiasSharpDefectConstant
      nlinarith
    calc
      |roughSaiasReverseNormalFormDefect X y X| ≤
          (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
            Real.log (y : ℝ) ^ 2 := hupper
      _ = (3 + 45 * roughSaiasThetaFourthPowerConstant) *
            ((X : ℝ) / Real.log (y : ℝ) ^ 2) := by ring
      _ ≤ roughSaiasSharpDefectConstant *
            ((X : ℝ) / Real.log (y : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hconst htargetNonneg
      _ = roughSaiasSharpDefectConstant * (X : ℝ) /
            Real.log (y : ℝ) ^ 2 := by ring
  · have hysqrt : y ≤ Nat.sqrt X + 1 := by omega
    have hMX : Nat.sqrt X + 1 ≤ X := by
      have htransition := roughSaiasSelectorTransition_le hX2 hyX.le
      exact (le_max_right y (Nat.sqrt X + 1)).trans htransition
    have hupperNat : X ≤ (Nat.sqrt X + 1) ^ 2 :=
      (Nat.lt_succ_sqrt' X).le
    have hbase :=
      roughSaiasReverseNormalFormDefect_abs_le_lowerNaturalCells_add_invLogSq
        hXpos hYtheta hy3 hyX le_rfl hu5 hysqrt hMX hupperNat
    have hlower :=
      abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq
        hXpos hy3 hysqrt hMX le_rfl hu5
    calc
      |roughSaiasReverseNormalFormDefect X y X| ≤
          |∑ m ∈ Finset.Ico y (Nat.sqrt X + 1),
              roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
            (3 + 243 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
              Real.log (y : ℝ) ^ 2 := hbase
      _ ≤ 40 * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
            (3 + 243 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
              Real.log (y : ℝ) ^ 2 := add_le_add hlower le_rfl
      _ = roughSaiasSharpDefectConstant * (X : ℝ) /
            Real.log (y : ℝ) ^ 2 := by
        unfold roughSaiasSharpDefectConstant
        ring

/-- The concrete constant and cutoff above satisfy the abstract sharp
reverse-normal-form defect interface used by endpoint induction. -/
theorem roughSaiasSharpReverseNormalFormDefectInvLogSqBound :
    RoughSaiasReverseNormalFormDefectInvLogSqBound
      roughSaiasSharpDefectConstant roughSaiasSharpDefectCutoff := by
  intro X y hY hy2 hyX hlog
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5 :=
    (div_le_iff₀ hlogy).2 hlog
  exact roughSaiasReverseNormalFormDefect_self_abs_le_sharp_invLogSq
    hY hyX hu5

/-- Unconditional paper-scale endpoint approximation obtained from the
closed sharp reverse-normal-form defect. -/
theorem roughSaiasSharpEndpointApproximationUpToFive :
    RoughSaiasEndpointApproximationUpToFive
      (roughSaiasInvLogSqEndpointRate roughSaiasSharpDefectConstant)
      (roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff) := by
  apply roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect
  · unfold roughSaiasSharpDefectConstant
    have hCtheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  · exact roughSaiasSharpReverseNormalFormDefectInvLogSqBound

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpFixedHeadIntervalShift -/
section


/-!
# Sharp fixed-head interval shifts

The endpointwise fixed-head estimate loses one logarithm because it takes
absolute values before subtracting the two endpoints of an interval.  This
file retains that subtraction.  The Dickman main terms are first compared
at the interval level; the two residual increments are then bounded by the
already-proved sharp Saias endpoint approximation.

No new analytic predicate is introduced.  In particular, the only
approximation used below is
`roughSaiasSharpEndpointApproximationUpToFive`.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## The interval-level Dickman cancellation -/









/-! ## Adding the two residual increments -/





/-! ## The closed inverse-log-square specialization -/





/-- Fully closed sharp fixed-divisor interval shift. -/
theorem roughFriableInterval_fixedDivisorShift_abs_le_sharp
    {A B y d : ℕ}
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y) (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |((FriableAsymptotic.friableCount (B / d) y : ℝ) -
          (FriableAsymptotic.friableCount (A / d) y : ℝ)) -
        ((FriableAsymptotic.friableCount B y : ℝ) -
          (FriableAsymptotic.friableCount A y : ℝ)) / (d : ℝ)| ≤
      roughSaiasSharpIntervalFixedDivisorBudget A B y d := by
  exact
    (roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation
      roughCompactBVTranslationPrinciple
      roughSaiasSharpEndpointApproximationUpToFive
      hY hy hd hdA hAB hlogB).trans
      (roughSaiasIntervalFixedDivisorShiftBudget_sharp_le hy hd hAB)

/-! ## Physical blocks and the finite head -/

/-- The literal two-piece physical block inherits the two
cancellation-preserving interval budgets. -/
theorem roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_sharp
    {lo split hi y d : ℕ} {alpha broad : ℝ}
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y) (hd : 0 < d) (hdLo : d ≤ lo)
    (hloSplit : lo ≤ split) (hSplitHi : split ≤ hi)
    (hlogHi : Real.log (hi : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad -
        roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
      |alpha| *
          roughSaiasSharpIntervalFixedDivisorBudget split hi y d +
        |broad| *
          roughSaiasSharpIntervalFixedDivisorBudget lo split y d := by
  have hlo : 0 < lo := hd.trans_le hdLo
  have hsplit : 0 < split := hlo.trans_le hloSplit
  have hdSplit : d ≤ split := hdLo.trans hloSplit
  have hlogSplit :
      Real.log (split : ℝ) ≤ 5 * Real.log (y : ℝ) := by
    have hmono : Real.log (split : ℝ) ≤ Real.log (hi : ℝ) :=
      Real.log_le_log (by exact_mod_cast hsplit)
        (by exact_mod_cast hSplitHi)
    exact hmono.trans hlogHi
  have hhigh :=
    roughFriableInterval_fixedDivisorShift_abs_le_sharp
      hY hy hd hdSplit hSplitHi hlogHi
  have hbroad :=
    roughFriableInterval_fixedDivisorShift_abs_le_sharp
      hY hy hd hdLo hloSplit hlogSplit
  let intervalError : ℕ → ℕ → ℝ := fun A B ↦
    ((FriableAsymptotic.friableCount (B / d) y : ℝ) -
        (FriableAsymptotic.friableCount (A / d) y : ℝ)) -
      ((FriableAsymptotic.friableCount B y : ℝ) -
        (FriableAsymptotic.friableCount A y : ℝ)) / (d : ℝ)
  have hblock :
      roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
            alpha broad -
          roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ) =
        alpha * intervalError split hi +
          broad * intervalError lo split := by
    rw [roughSmoothPhysicalBlock_eq_friableEndpoints
        (Nat.div_le_div_right hloSplit)
        (Nat.div_le_div_right hSplitHi),
      roughSmoothPhysicalBlock_eq_friableEndpoints hloSplit hSplitHi]
    dsimp [intervalError]
    ring
  have hhigh' :
      |intervalError split hi| ≤
        roughSaiasSharpIntervalFixedDivisorBudget split hi y d := by
    simpa only [intervalError] using hhigh
  have hbroad' :
      |intervalError lo split| ≤
        roughSaiasSharpIntervalFixedDivisorBudget lo split y d := by
    simpa only [intervalError] using hbroad
  rw [hblock]
  calc
    |alpha * intervalError split hi +
        broad * intervalError lo split| ≤
      |alpha| * |intervalError split hi| +
        |broad| * |intervalError lo split| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
    _ ≤ |alpha| *
          roughSaiasSharpIntervalFixedDivisorBudget split hi y d +
        |broad| *
          roughSaiasSharpIntervalFixedDivisorBudget lo split y d :=
      add_le_add
        (mul_le_mul_of_nonneg_left hhigh' (abs_nonneg alpha))
        (mul_le_mul_of_nonneg_left hbroad' (abs_nonneg broad))

/-- A smooth physical block is bounded by its right endpoint times the
sum of the two absolute weights. -/
theorem roughSmoothPhysicalBlock_abs_le_rightEndpoint
    {lo split hi y : ℕ} {alpha broad : ℝ}
    (hSplitHi : split ≤ hi) :
    |roughSmoothPhysicalBlock lo split hi y alpha broad| ≤
      (|alpha| + |broad|) * (hi : ℝ) := by
  have hsmoothCard :
      ∀ A B : ℕ,
        ((Erdos390.Full.StructuredCells.smoothInterval A B y).card : ℝ) ≤
          (B : ℝ) := by
    intro A B
    have hsubset :
        Erdos390.Full.StructuredCells.smoothInterval A B y ⊆
          Finset.Ioc A B := by
      intro a ha
      have haData :=
        Erdos390.Full.StructuredCells.mem_smoothInterval.mp ha
      exact Finset.mem_Ioc.mpr ⟨haData.1, haData.2.1⟩
    have hcard :
        (Erdos390.Full.StructuredCells.smoothInterval A B y).card ≤
          (Finset.Ioc A B).card :=
      Finset.card_le_card hsubset
    calc
      ((Erdos390.Full.StructuredCells.smoothInterval A B y).card : ℝ) ≤
          ((Finset.Ioc A B).card : ℝ) := by exact_mod_cast hcard
      _ = ((B - A : ℕ) : ℝ) := by rw [Nat.card_Ioc]
      _ ≤ (B : ℝ) := by exact_mod_cast Nat.sub_le B A
  have hhighCard :
      ((Erdos390.Full.StructuredCells.smoothInterval split hi y).card : ℝ) ≤
        (hi : ℝ) :=
    hsmoothCard split hi
  have hbroadCard :
      ((Erdos390.Full.StructuredCells.smoothInterval lo split y).card : ℝ) ≤
        (hi : ℝ) :=
    (hsmoothCard lo split).trans (by exact_mod_cast hSplitHi)
  unfold roughSmoothPhysicalBlock
  calc
    |alpha *
          ((Erdos390.Full.StructuredCells.smoothInterval split hi y).card : ℝ) +
        broad *
          ((Erdos390.Full.StructuredCells.smoothInterval lo split y).card : ℝ)| ≤
      |alpha *
          ((Erdos390.Full.StructuredCells.smoothInterval split hi y).card : ℝ)| +
        |broad *
          ((Erdos390.Full.StructuredCells.smoothInterval lo split y).card : ℝ)| :=
      abs_add_le _ _
    _ =
      |alpha| *
          ((Erdos390.Full.StructuredCells.smoothInterval split hi y).card : ℝ) +
      |broad| *
          ((Erdos390.Full.StructuredCells.smoothInterval lo split y).card : ℝ) := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (show 0 ≤
          ((Erdos390.Full.StructuredCells.smoothInterval split hi y).card : ℝ) by
            exact_mod_cast Nat.zero_le
              (Erdos390.Full.StructuredCells.smoothInterval split hi y).card
        ),
        abs_of_nonneg (show 0 ≤
          ((Erdos390.Full.StructuredCells.smoothInterval lo split y).card : ℝ) by
            exact_mod_cast Nat.zero_le
              (Erdos390.Full.StructuredCells.smoothInterval lo split y).card
        )]
    _ ≤ |alpha| * (hi : ℝ) + |broad| * (hi : ℝ) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hhighCard (abs_nonneg alpha))
        (mul_le_mul_of_nonneg_left hbroadCard (abs_nonneg broad))
    _ = (|alpha| + |broad|) * (hi : ℝ) := by ring

/-- If the entire physical row lies below `2d`, both the divided and
undivided blocks have uniformly bounded fixed-divisor shift.  This is the
small-row branch needed when the fixed head modulus does not fit below the
lower endpoint. -/
theorem roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_small
    {lo split hi y d : ℕ} {alpha broad : ℝ}
    (hd : 0 < d) (_hloSplit : lo ≤ split) (hSplitHi : split ≤ hi)
    (hhi : hi ≤ 2 * d) :
    |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad -
        roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
      4 * (|alpha| + |broad|) := by
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hweight : 0 ≤ |alpha| + |broad| :=
    add_nonneg (abs_nonneg alpha) (abs_nonneg broad)
  have hquotientHi :
      (((hi / d : ℕ) : ℝ)) ≤ 2 := by
    calc
      (((hi / d : ℕ) : ℝ)) ≤ (hi : ℝ) / (d : ℝ) :=
        Nat.cast_div_le
      _ ≤ 2 := by
        apply (div_le_iff₀ hdReal).2
        exact_mod_cast hhi
  have hsmall :
      |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad| ≤
        (|alpha| + |broad|) * ((hi / d : ℕ) : ℝ) :=
    roughSmoothPhysicalBlock_abs_le_rightEndpoint
      (lo := lo / d) (split := split / d) (hi := hi / d) (y := y)
      (alpha := alpha) (broad := broad)
      (Nat.div_le_div_right (c := d) hSplitHi)
  have hlarge :
      |roughSmoothPhysicalBlock lo split hi y alpha broad| ≤
        (|alpha| + |broad|) * (hi : ℝ) :=
    roughSmoothPhysicalBlock_abs_le_rightEndpoint
      (lo := lo) (split := split) (hi := hi) (y := y)
      (alpha := alpha) (broad := broad) hSplitHi
  have hsmall' :
      |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad| ≤
        2 * (|alpha| + |broad|) := by
    calc
      _ ≤ (|alpha| + |broad|) * ((hi / d : ℕ) : ℝ) := hsmall
      _ ≤ (|alpha| + |broad|) * 2 :=
        mul_le_mul_of_nonneg_left hquotientHi hweight
      _ = 2 * (|alpha| + |broad|) := by ring
  have hlarge' :
      |roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
        2 * (|alpha| + |broad|) := by
    rw [abs_div, abs_of_pos hdReal]
    calc
      |roughSmoothPhysicalBlock lo split hi y alpha broad| / (d : ℝ) ≤
          ((|alpha| + |broad|) * (hi : ℝ)) / (d : ℝ) := by
        exact (div_le_div_iff_of_pos_right hdReal).2 hlarge
      _ = (|alpha| + |broad|) * ((hi : ℝ) / (d : ℝ)) := by ring
      _ ≤ (|alpha| + |broad|) * 2 := by
        apply mul_le_mul_of_nonneg_left _ hweight
        exact (div_le_iff₀ hdReal).2 (by exact_mod_cast hhi)
      _ = 2 * (|alpha| + |broad|) := by ring
  calc
    |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad -
        roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
      |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad| +
        |roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| :=
      abs_sub _ _
    _ ≤ 2 * (|alpha| + |broad|) +
        2 * (|alpha| + |broad|) :=
      add_le_add hsmall' hlarge'
    _ = 4 * (|alpha| + |broad|) := by ring







/-- The literal canonical fixed-head ledger is controlled on every active
row, without assuming that the fixed modulus lies below the row endpoint.
The small-row branch is purely finite and contributes only a
head-dependent constant after the divisor sum. -/
theorem roughCanonicalFixedHeadShiftLedger_le_sharpIntervalBudget_allRows
    {W n h K y : ℕ} {alpha beta L : ℝ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y) (hKh : K * h ≤ n)
    (hlogHi :
      Real.log (((2 * n) / row.1 : ℕ) : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    roughCanonicalFixedHeadShiftLedger
        W n h K y alpha beta L row ≤
      roughCanonicalSharpFixedHeadShiftBudgetAllRows
        W n h K y alpha beta L row := by
  have hlabel : 0 < row.1 :=
    canonicalCompleteRoughRow_label_pos y
      (roughRawCandidateSet n h K) row
  have hloSplit :
      n / row.1 ≤ (2 * n - K * h) / row.1 := by
    apply Nat.div_le_div_right
    omega
  have hSplitHi :
      (2 * n - K * h) / row.1 ≤ (2 * n) / row.1 :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  unfold roughCanonicalFixedHeadShiftLedger
    roughCanonicalSharpFixedHeadShiftBudgetAllRows
  apply Finset.sum_le_sum
  intro d hdMem
  have hd : 0 < d := Nat.pos_of_mem_divisors hdMem
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  by_cases hdLo : d ≤ n / row.1
  · rw [if_pos hdLo]
    exact roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_sharp
      hY hy hd hdLo hloSplit hSplitHi hlogHi
  · rw [if_neg hdLo]
    have hloD : n / row.1 < d := Nat.lt_of_not_ge hdLo
    have hnD : n < d * row.1 :=
      (Nat.div_lt_iff_lt_mul hlabel).mp hloD
    have htwo :
        2 * n < (2 * d) * row.1 := by
      have hmul :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnD
      simpa only [Nat.mul_assoc] using hmul
    have hhiLt : (2 * n) / row.1 < 2 * d :=
      (Nat.div_lt_iff_lt_mul hlabel).mpr htwo
    exact roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_small
      hd hloSplit hSplitHi hhiLt.le

/-- Raw-row quota closure with the analytic endpoint input and the entire
fixed-head shift discharged by the closed sharp theorems in this file.
Only the three explicit finite ledgers remain to be absorbed into the
chosen paper allowance. -/
theorem roughCanonicalRawRowQuotaError_abs_le_three_mul_sharpAllowance
    {W n h K y : ℕ} {alpha beta L E : ℝ}
    (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W) alpha beta L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (htransition : roughPhysicalSaiasTransitionBudget
        (roughSaiasInvLogSqEndpointRate roughSaiasSharpDefectConstant)
        (roughHeadDensity W) alpha beta L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (hhead :
      roughCanonicalSharpFixedHeadShiftBudgetAllRows
        W n h K y alpha beta L row ≤ E) :
    |roughCanonicalRawRowQuotaError
        W n h K y alpha beta L row| ≤ 3 * E := by
  have hheadLedger :
      roughCanonicalFixedHeadShiftLedger
          W n h K y alpha beta L row ≤ E :=
    (roughCanonicalFixedHeadShiftLedger_le_sharpIntervalBudget_allRows
      row hY hy hKh (hlogs (1 : Fin 4))).trans hhead
  exact roughCanonicalRawRowQuotaError_abs_le_three_mul_paperAllowance
    roughCompactBVTranslationPrinciple hWy row hrowN hKh
      roughSaiasSharpEndpointApproximationUpToFive hY hy hlogs
      hmain htransition hheadLedger

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.RoughSaiasSharpCanonicalRowPaperScale -/
section


/-!
# Canonical sharp Saias row-scale geometry

This file specializes the closed sharp endpoint and fixed-head estimates to
the paper's literal balanced raw point.  The high-block multiplicity is
written as `K0 + 1`, so its positivity is built into the data rather than
assumed separately.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Uniform control of the literal balanced coefficient -/







/-! ## Fixed constants for the three row ledgers -/



theorem roughBalancedAlphaConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughBalancedAlphaConstant W K0 c beta := by
  unfold roughBalancedAlphaConstant
  have hK : (0 : ℝ) <
      (((K0 + 1 : ℕ) : ℝ)) := by positivity
  have hdelta : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  positivity











/-! ## Quotient and logarithmic geometry -/





























/-! ## The balanced Dickman main ledger -/





/-! ## The weighted sharp Saias transition ledger -/



/-! ## Absorption of the sharp fixed-head divisor sum -/



/-! ## One unified canonical raw-row allowance -/

theorem roughCanonicalSharpMainRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughCanonicalSharpMainRowScaleConstant W K0 c beta := by
  unfold roughCanonicalSharpMainRowScaleConstant
  have hA :=
    roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc
  have hK : (0 : ℝ) ≤ (((K0 + 1 : ℕ) : ℝ)) := by positivity
  positivity

theorem roughCanonicalSharpTransitionRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughCanonicalSharpTransitionRowScaleConstant W K0 c beta := by
  unfold roughCanonicalSharpTransitionRowScaleConstant
  have hA :=
    roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc
  have hC : 0 ≤ roughSaiasSharpDefectConstant := by
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  positivity

theorem roughCanonicalSharpHeadDivisorRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {d : ℕ} (hd : 0 < d) :
    0 ≤ roughCanonicalSharpHeadDivisorRowScaleConstant
      W K0 d c beta := by
  unfold roughCanonicalSharpHeadDivisorRowScaleConstant
  have hA :=
    roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc
  have hC : 0 ≤ roughSaiasSharpDefectConstant := by
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  positivity

theorem roughCanonicalSharpHeadRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughCanonicalSharpHeadRowScaleConstant W K0 c beta := by
  unfold roughCanonicalSharpHeadRowScaleConstant
  apply Finset.sum_nonneg
  intro d hdMem
  exact mul_nonneg (abs_nonneg _)
    (roughCanonicalSharpHeadDivisorRowScaleConstant_nonneg
      W K0 (beta := beta) hc (Nat.pos_of_mem_divisors hdMem))



/-- The balanced literal raw row is controlled by one fixed
`C_W * (Xrow/L²+1)` allowance after all three analytic ledgers have been
discharged. -/
theorem roughCanonicalBalancedRawRowQuotaError_abs_le_unified
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n y : ℕ} (hn : 2 ≤ n)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)))
    (hrowN : row.1 ≤ n)
    (hWy : W ≤ y)
    (hY :
      roughSaiasInvLogSqEndpointCutoff
        roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y)
    (hLone : 1 ≤ L n)
    (hlogY : L n / 5 ≤ Real.log (y : ℝ))
    (htail :
      (upperTailLength c n : ℝ) ≤
        2 * c * (n : ℝ) / L n)
    (hKh :
      (K0 + 1) * upperTailLength c n ≤ n)
    (htailPos : 0 < upperTailLength c n)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    |roughCanonicalRawRowQuotaError
        W n (upperTailLength c n) (K0 + 1) y
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n) row| ≤
      3 * (roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta *
        ((((n / row.1 : ℕ) : ℝ)) / L n ^ 2 + 1)) := by
  let S : ℝ := (((n / row.1 : ℕ) : ℝ)) / L n ^ 2 + 1
  have hx0 : 0 ≤ (((n / row.1 : ℕ) : ℝ)) :=
    Nat.cast_nonneg _
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    exact add_nonneg
      (div_nonneg hx0 (sq_nonneg (L n))) (by norm_num)
  have hmain0 :=
    roughCanonicalSharpMainRowScaleConstant_nonneg
      W K0 (beta := beta) hc
  have htransition0 :=
    roughCanonicalSharpTransitionRowScaleConstant_nonneg
      W K0 (beta := beta) hc
  have hhead0 :=
    roughCanonicalSharpHeadRowScaleConstant_nonneg
      W K0 (beta := beta) hc
  have hmainBase :=
    roughCanonicalBalancedDickmanTransitionLedger_le
      W K0 (beta := beta) (n := n) (r := row.1) (y := y)
      hc hn
      (canonicalCompleteRoughRow_label_pos y
        (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) row)
      hrowN hy hLone hlogY htail hKh htailPos
  have htransitionBase :=
    roughCanonicalBalancedSaiasTransitionBudget_le
      W K0 (beta := beta) (n := n) (r := row.1) (y := y)
      hc hn
      (canonicalCompleteRoughRow_label_pos y
        (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) row)
      hrowN hy hLone hlogY htail hKh
  have hheadBase :=
    roughCanonicalBalancedSharpFixedHeadBudget_le
      W K0 (beta := beta) (n := n) (y := y)
      hc hn hy row hrowN hLone hlogY htail hKh
  have hmain :
      roughPhysicalDickmanTransitionLedger
          (roughHeadDensity W)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n)
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) y ≤
        roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta * S := by
    apply hmainBase.trans
    apply mul_le_mul_of_nonneg_right _ hS0
    unfold roughCanonicalSharpUnifiedRowScaleConstant
    linarith
  have htransition :
      roughPhysicalSaiasTransitionBudget
          (roughSaiasInvLogSqEndpointRate
            roughSaiasSharpDefectConstant)
          (roughHeadDensity W)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n)
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) y ≤
        roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta * S := by
    apply htransitionBase.trans
    apply mul_le_mul_of_nonneg_right _ hS0
    unfold roughCanonicalSharpUnifiedRowScaleConstant
    linarith
  have hhead :
      roughCanonicalSharpFixedHeadShiftBudgetAllRows
          W n (upperTailLength c n) (K0 + 1) y
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n) row ≤
        roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta * S := by
    apply hheadBase.trans
    apply mul_le_mul_of_nonneg_right _ hS0
    unfold roughCanonicalSharpUnifiedRowScaleConstant
    linarith
  simpa only [S] using
    (roughCanonicalRawRowQuotaError_abs_le_three_mul_sharpAllowance
      hWy row hrowN hKh hY hy hlogs hmain htransition hhead)

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.BankPaperCanonicalNonsmoothSlackClosure -/
section


/-!
# Canonical nonsmooth endpoint-slack closure

This module connects the sharp balanced raw-row estimate to the literal
guarded constant-pool correction used at the actual Proposition 8.7
endpoint.

There are two finite guard estimates.  The sharp one assumes the usual
raw-point box and proves that passing through all numerical guards changes
one active row discrepancy by at most `2`.  The assumption-free one uses
the already proved uniform absolute bound for the balanced coefficient and
gives a fixed (slightly larger) numerator constant.  The latter is the
version used in the eventual theorem, so no unproved eventual feasibility
of `roughHeadBalancedAlpha` is hidden in the endpoint-slack conclusion.

The final bounds use the paper split

`beta = betaProt + betaAct`, `0 < betaAct`, `sigma <= betaProt`.

Thus the lower nonsmooth margin has the fixed strict reserve `betaAct/L`.
The upper margin follows once `L` exceeds the fixed sum of the parameters.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.Scale
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Filter Topology
open scoped BigOperators

noncomputable section

namespace BankPaperRealization

/-! ## Active rows contain no fixed exceptional factor -/









/-! ## The sharp finite `+2` guard numerator -/



/-! ## An assumption-free fixed guard numerator -/













end BankPaperRealization

/-! ## Eventual sharp raw-row estimate on every active canonical row -/

private theorem nonsmoothSlack_L_tendsto_atTop :
    Tendsto L atTop atTop := by
  simpa only [L] using
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem nonsmoothSlack_rpow_tendsto_atTop
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => (n : Real) ^ deltaStar) atTop atTop := by
  exact (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop

/-- A nontrivial intrinsic rough label is at least three once the cutoff
contains the prime two. -/
theorem isCompleteRoughLabel_three_le_of_two_le
    {y label : Nat} (hy : 2 <= y)
    (hlabel : IsCompleteRoughLabel y label) (hlabelNe : label ≠ 1) :
    3 <= label := by
  have hlabelPos : 0 < label := hlabel.1
  have hlabelNeTwo : label ≠ 2 := by
    intro htwo
    subst label
    have hfactor :
        (2 : Nat).factorization 2 ≠ 0 :=
      (Nat.prime_two.factorization_pos_of_dvd (by norm_num)
        (dvd_refl 2)).ne'
    have hhigh := hlabel.2 2 hfactor
    omega
  omega

/-- The theorem `roughCanonicalBalancedRawRowQuotaError_abs_le_unified`
with all of its paper-scale endpoint hypotheses discharged uniformly on
active rows. -/
theorem eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active
    (W K0 : Nat) {c beta deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall row : CanonicalCompleteRoughRow (yNat n)
        (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)),
      BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel
          n deltaStar row.1 ->
        |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
            (K0 + 1) (yNat n)
            (roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n))
            beta (L n) row| <=
          3 * (roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta *
            ((((n / row.1 : Nat) : Real)) / L n ^ 2 + 1)) := by
  have hLOne : ∀ᶠ n : Nat in atTop, 1 <= L n :=
    nonsmoothSlack_L_tendsto_atTop.eventually (eventually_ge_atTop 1)
  have hpower : ∀ᶠ n : Nat in atTop,
      (12 : Real) <= (n : Real) ^ deltaStar :=
    (nonsmoothSlack_rpow_tendsto_atTop hdelta).eventually
      (eventually_ge_atTop 12)
  have htailRatio : ∀ᶠ n : Nat in atTop,
      (K0 + 1 : Real) *
          ((upperTailLength c n : Real) / (n : Real)) < 1 := by
    have hT :=
      (upperTailLength_ratio_tendsto_zero hc).const_mul (K0 + 1 : Real)
    exact hT.eventually
      (eventually_lt_nhds (by
        simp : (K0 + 1 : Real) * 0 < 1))
  filter_upwards [
      eventually_ge_atTop 2,
      eventually_bankAnchor_fixed_le_yNat W,
      eventually_bankAnchor_fixed_le_yNat
        (roughSaiasInvLogSqEndpointCutoff
          roughSaiasSharpDefectCutoff),
      eventually_bankBottom_six_le_yNat,
      hLOne,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc,
      eventually_upperTailLength_pos hc,
      htailRatio,
      hpower]
      with n hn hWy hY hySix hLone hlogFace htailScale htailPos
        htailRatioN hpowerN
  intro row hactive
  have hnPos : 0 < n := by omega
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
  have hlabelData :=
    isCompleteRoughLabel_of_canonicalCompleteRoughRow row
  have hlabelPos : 0 < row.1 := hlabelData.1
  have hlabelThree : 3 <= row.1 :=
    isCompleteRoughLabel_three_le_of_two_le (by omega) hlabelData hactive.1
  have hlabelSmall : 6 * row.1 <= n :=
    roughCanonical_activeLabel_three_mul_le_half hnPos hlabelPos hactive.2
      hpowerN
  have hrowN : row.1 <= n := by omega
  have hKhReal :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <
        (n : Real) := by
    have hdiv :
        ((K0 + 1 : Real) * (upperTailLength c n : Real)) /
            (n : Real) < 1 := by
      simpa only [mul_div_assoc] using htailRatioN
    have hcross :=
      (div_lt_iff₀ hnReal).mp hdiv
    push_cast
    simpa only [one_mul] using hcross
  have hKh : (K0 + 1) * upperTailLength c n <= n := by
    exact_mod_cast hKhReal.le
  have htailLe : upperTailLength c n <= n :=
    (Nat.le_mul_of_pos_left _ (by omega : 0 < K0 + 1)).trans hKh
  have hdivLe :
      forall numerator : Nat, numerator <= 3 * n ->
        numerator / row.1 <= n := by
    intro numerator hnumerator
    calc
      numerator / row.1 <= (3 * n) / row.1 :=
        Nat.div_le_div_right hnumerator
      _ <= (3 * n) / 3 :=
        Nat.div_le_div_left (a := 3 * n) hlabelThree (by norm_num)
      _ = n := by omega
  have hdivPos :
      forall numerator : Nat, n <= numerator ->
        0 < numerator / row.1 := by
    intro numerator hnumerator
    exact Nat.div_pos (hrowN.trans hnumerator) hlabelPos
  have hendpointLe : forall i : Fin 4,
      roughPhysicalNatEndpoint
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) i <= n := by
    intro i
    fin_cases i <;> simp [roughPhysicalNatEndpoint] <;>
      apply hdivLe <;> omega
  have hendpointPos : forall i : Fin 4,
      0 < roughPhysicalNatEndpoint
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) i := by
    intro i
    fin_cases i
    · change 0 < (2 * n + upperTailLength c n) / row.1
      exact hdivPos _ (by omega)
    · change 0 < (2 * n) / row.1
      exact hdivPos _ (by omega)
    · change
        0 < (2 * n - (K0 + 1) * upperTailLength c n) / row.1
      exact hdivPos _ (by omega)
    · change 0 < n / row.1
      exact hdivPos _ (le_refl n)
  have hlogs : forall i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) i : Real) <=
        5 * Real.log (yNat n : Real) := by
    intro i
    have hlogLe : Real.log (roughPhysicalNatEndpoint
        ((2 * n + upperTailLength c n) / row.1)
        ((2 * n) / row.1)
        ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
        (n / row.1) i : Real) <= L n := by
      unfold L
      exact Real.log_le_log
        (by exact_mod_cast hendpointPos i)
        (by exact_mod_cast hendpointLe i)
    nlinarith [hlogFace]
  apply roughCanonicalBalancedRawRowQuotaError_abs_le_unified
    W K0 (beta := beta) hc hn row hrowN hWy hY (by omega) hLone
  · nlinarith [hlogFace]
  · calc
      (upperTailLength c n : Real) <=
          2 * c * secondOrderScale n := htailScale
      _ = 2 * c * (n : Real) / L n := by
        unfold secondOrderScale L
        ring
  · exact hKh
  · exact htailPos
  · exact hlogs

namespace BankPaperRealization

/-! ## From the raw numerator to the guarded correction density -/











/-! ## The eventual paper beta/sigma nonsmooth bounds -/













end BankPaperRealization

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_007 := by
  exact @Erdos390.WholePaper.eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active
