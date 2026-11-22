-- Prove2me | solution 1 for Erdos390.WholePaper.exists_eventually_centralAnchorCertificate_compact
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-17T17:41:37.614946+00:00
-- url     : https://prove2.me/submissions/377f59e5-b8cd-4f6b-ac61-f2663653bbea

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
import Theorems.Thm_Erdos390_WholePaper_residualPromotionCost_fixedCutoff_uniform_bound

/- Source module: Erdos390.WholePaper.SafePrimeCounting -/
section


/-!
# A prime-counting asymptotic with an audited dependency closure

The pinned auxiliary package contains stronger convenience theorems whose
transitive imports include unfinished declarations.  This file instead
derives `π(x) ~ x / log x` from the already audited `MediumPNT` route used by
`FriableAsymptotic.theta_error_isBigO_log_power` and Mathlib's elementary
comparison between `π` and `θ`.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

private theorem div_log_isLittleO_id :
    (fun x : ℝ => x / Real.log x) =o[atTop] (fun x : ℝ => x) := by
  apply (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr
  apply Real.tendsto_log_atTop.inv_tendsto_atTop.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  exact inv_mul_cancel₀ hlog

private theorem div_log_sq_isLittleO_div_log :
    (fun x : ℝ => x / Real.log x ^ 2) =o[atTop]
      (fun x : ℝ => x / Real.log x) := by
  apply (isLittleO_iff_tendsto (fun x hx => by
    apply div_eq_zero_iff.mpr
    rcases (div_eq_zero_iff.mp hx) with hx | hx
    · exact Or.inl hx
    · exact Or.inr (by simp [hx]))).mpr
  apply Real.tendsto_log_atTop.inv_tendsto_atTop.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hx)
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp
  exact inv_mul_cancel₀ hlog

theorem theta_sub_id_isLittleO :
    (Chebyshev.theta - id) =o[atTop] (id : ℝ → ℝ) := by
  have htheta :
      (Chebyshev.theta - id) =O[atTop]
        (fun x : ℝ => x / Real.log x) := by
    simpa using
      Erdos390.Full.FriableAsymptotic.theta_error_isBigO_log_power 1
  exact htheta.trans_isLittleO div_log_isLittleO_id

theorem theta_div_log_sub_main_isLittleO :
    (fun x : ℝ =>
      Chebyshev.theta x / Real.log x - x / Real.log x) =o[atTop]
        (fun x : ℝ => x / Real.log x) := by
  have hmul := theta_sub_id_isLittleO.mul_isBigO
    (isBigO_refl (fun x : ℝ => (Real.log x)⁻¹) atTop)
  apply hmul.congr'
  · exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, id_eq]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
  · exact Eventually.of_forall fun x => by
      simp only [id_eq]
      rw [div_eq_mul_inv]

theorem primeCounting_sub_main_isLittleO :
    (fun x : ℝ =>
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) =o[atTop]
        (fun x : ℝ => x / Real.log x) := by
  have hpi :
      (fun x : ℝ =>
        (Nat.primeCounting ⌊x⌋₊ : ℝ) -
          Chebyshev.theta x / Real.log x) =o[atTop]
          (fun x : ℝ => x / Real.log x) :=
    Chebyshev.primeCounting_sub_theta_div_log_isBigO.trans_isLittleO
      div_log_sq_isLittleO_div_log
  have hadd := hpi.add theta_div_log_sub_main_isLittleO
  apply hadd.congr' (Eventually.of_forall fun x => by ring) (Eventually.of_forall fun _ => rfl)

/-- Safe real-variable prime number theorem. -/
theorem primeCounting_real_isEquivalent :
    (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x : ℝ => x / Real.log x) :=
  primeCounting_sub_main_isLittleO



end Erdos390.WholePaper.SafePrimeCounting

end

/- Source module: Erdos390.WholePaper.ScaledPrimeCounting -/
section


/-!
# Prime counting at fixed positive dilates

This is the uniformity-free fixed-scale consequence needed for each of the
thirteen lower-bound layers.  Moving endpoints will later be sandwiched
between fixed dilates.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

theorem tendsto_log_natCast_atTop :
    Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_log_natCast_div_log_const_mul (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun n : ℕ =>
        Real.log (n : ℝ) / Real.log (a * (n : ℝ)))
      atTop (nhds 1) := by
  have hsmall : Tendsto
      (fun n : ℕ => Real.log a / Real.log (n : ℝ))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_natCast_atTop
  have hden : Tendsto
      (fun n : ℕ => 1 + Real.log a / Real.log (n : ℝ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hsmall
  have hinv : Tendsto
      (fun n : ℕ => 1 / (1 + Real.log a / Real.log (n : ℝ)))
      atTop (nhds 1) := by
    have hnum : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    convert hnum.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
    norm_num
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlogn : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  rw [Real.log_mul ha.ne' hnR.ne']
  field_simp
  ring

theorem div_log_const_mul_isEquivalent (a : ℝ) (ha : 0 < a) :
    (fun n : ℕ =>
      (a * (n : ℝ)) / Real.log (a * (n : ℝ))) ~[atTop]
      (fun n : ℕ =>
        (a * (n : ℝ)) / Real.log (n : ℝ)) := by
  have hscaleTop :
      Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have htargetNe :
      ∀ᶠ n : ℕ in atTop,
        (a * (n : ℝ)) / Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    exact div_ne_zero (mul_ne_zero ha.ne' hnR.ne')
      (Real.log_pos (by exact_mod_cast hn)).ne'
  apply (isEquivalent_iff_tendsto_one htargetNe).mpr
  apply (tendsto_log_natCast_div_log_const_mul a ha).congr'
  filter_upwards [eventually_gt_atTop 1,
      hscaleTop.eventually (eventually_gt_atTop 1)] with n hn han
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlogn : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogaN : Real.log (a * (n : ℝ)) ≠ 0 := (Real.log_pos han).ne'
  have han0 : a * (n : ℝ) ≠ 0 := mul_ne_zero ha.ne' hnR.ne'
  change Real.log (n : ℝ) / Real.log (a * (n : ℝ)) =
    ((a * (n : ℝ)) / Real.log (a * (n : ℝ))) /
      ((a * (n : ℝ)) / Real.log (n : ℝ))
  field_simp

/-- For each fixed `a>0`, the count of primes up to `a n` has the expected
`a n / log n` asymptotic. -/
theorem primeCounting_const_mul_nat_isEquivalent (a : ℝ) (ha : 0 < a) :
    (fun n : ℕ =>
      (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ)) ~[atTop]
      (fun n : ℕ =>
        (a * (n : ℝ)) / Real.log (n : ℝ)) := by
  have hscaleTop :
      Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  exact (primeCounting_real_isEquivalent.comp_tendsto hscaleTop).trans
    (div_log_const_mul_isEquivalent a ha)

end Erdos390.WholePaper.SafePrimeCounting

end

/- Source module: Erdos390.WholePaper.PrimeLayerCounts -/
section


/-!
# Fixed prime-interval counts

This converts the safe fixed-dilate PNT into the exact difference form used
by each stationary layer of Section 3.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

private theorem eventually_secondOrderScale_ne_zero :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / Real.log (n : ℝ) ≠ 0 := by
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  exact div_ne_zero hnPos.ne'
    (Real.log_pos (by exact_mod_cast hn)).ne'

theorem primeCounting_const_mul_normalized_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun n : ℕ =>
        (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds a) := by
  have hdenNe :
      ∀ᶠ n : ℕ in atTop,
        (a * (n : ℝ)) / Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    exact div_ne_zero (mul_ne_zero ha.ne' hnPos.ne')
      (Real.log_pos (by exact_mod_cast hn)).ne'
  have hone := (isEquivalent_iff_tendsto_one hdenNe).mp
    (primeCounting_const_mul_nat_isEquivalent a ha)
  have hmul := hone.const_mul a
  have hmul' : Tendsto
      (fun n : ℕ =>
        a * ((Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
          ((a * (n : ℝ)) / Real.log (n : ℝ))))
      atTop (nhds a) := by
    simpa only [mul_one] using hmul
  apply hmul'.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  change
    a * ((Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
        ((a * (n : ℝ)) / Real.log (n : ℝ))) =
      (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))
  field_simp

theorem primeCounting_interval_normalized_tendsto
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun n : ℕ =>
        ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ : ℝ) -
          (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ)) /
            ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (b - a)) := by
  have hsub := (primeCounting_const_mul_normalized_tendsto b hb).sub
    (primeCounting_const_mul_normalized_tendsto a ha)
  apply hsub.congr'
  filter_upwards [eventually_secondOrderScale_ne_zero] with n hn
  field_simp

/-- Natural-cardinality version for the prime interval `(a n, b n]`. -/
theorem primeCounting_interval_natSub_normalized_tendsto
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto
      (fun n : ℕ =>
        ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ -
            Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (b - a)) := by
  have hb : 0 < b := ha.trans_le hab
  apply (primeCounting_interval_normalized_tendsto ha hb).congr'
  exact Eventually.of_forall fun n => by
    have harg : a * (n : ℝ) ≤ b * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n)
    have hfloor : ⌊a * (n : ℝ)⌋₊ ≤ ⌊b * (n : ℝ)⌋₊ :=
      Nat.floor_mono harg
    have hpi := Nat.monotone_primeCounting hfloor
    change
      ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ : ℝ) -
          (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ)) =
        ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ -
          Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))
    rw [Nat.cast_sub hpi]

end Erdos390.WholePaper.SafePrimeCounting

end

/- Source module: Erdos390.WholePaper.Complement -/
section


/-!
# Exact complement formulation

This proves the complement lemma immediately following the main theorem in
the paper.  All divisions occur in `ℚ`; the proof also exports the integral
cross-multiplication form used by later valuation arguments.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section





/-- Product of every integer in `(n,M]`, without truncated division. -/
theorem factorInterval_prod_mul_factorial {n M : ℕ} (hnM : n ≤ M) :
    (factorInterval n M).prod id * n.factorial = M.factorial := by
  induction M, hnM using Nat.le_induction with
  | base => simp [factorInterval]
  | succ M hnM ih =>
      rw [factorInterval, Finset.prod_Ioc_succ_top hnM, Nat.factorial_succ]
      change ((Finset.Ioc n M).prod id * (M + 1)) * n.factorial =
        (M + 1) * M.factorial
      calc
        ((Finset.Ioc n M).prod id * (M + 1)) * n.factorial =
            (M + 1) * ((Finset.Ioc n M).prod id * n.factorial) := by
              ac_rfl
        _ = (M + 1) * M.factorial := by
          rw [show (Finset.Ioc n M).prod id * n.factorial = M.factorial by
            simpa [factorInterval] using ih]







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.PrimeLayers -/
section


/-!
# Exact prime-layer arithmetic for the lower bound

This file contains only finite identities.  Analytic estimates for the
cardinalities of the layers are kept separate.  Cross-multiplied endpoint
conditions avoid all ambiguity from natural-number division at rational
endpoints.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section











/-- Above the square-root cutoff, Legendre's sum has only its first term. -/
theorem factorial_factorization_eq_div_of_lt_sq {m p : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmSq : m < p ^ 2) :
    m.factorial.factorization p = m / p := by
  rw [Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow hm.ne' hmSq)]
  simp





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.LargePrimeCollision -/
section


/-! Exact collision exclusion for the thirteen large-prime layers. -/

namespace Erdos390.WholePaper

/-- An integer below `L²` cannot contain two distinct primes at least `L`. -/
theorem not_two_distinct_large_primes_dvd
    {p q a L B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hLp : L ≤ p) (hLq : L ≤ q)
    (ha : 0 < a) (haB : a ≤ B) (hBL : B < L * L) :
    ¬(p ∣ a ∧ q ∣ a) := by
  rintro ⟨hpa, hqa⟩
  have hpqa : p * q ∣ a := hp.dvd_mul_of_dvd_ne hpq hq hpa hqa
  have hpq_le : p * q ≤ a := Nat.le_of_dvd ha hpqa
  have hLL_le : L * L ≤ p * q := Nat.mul_le_mul hLp hLq
  omega



end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.Constants -/
section


/-!
# Exact constants for Sections 3 and 4

This file records the thirteen lower-bound row masses, the nine small
primes, and the exact rational value of the paper's constant.  The same row
mass is used by the cofactor allocation in Section 4.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section











/-- The row mass is the exact difference of the two layer endpoints. -/
theorem two_div_sub_one_div_eq_alpha (r : ℕ) :
    (2 : ℚ) / (2 * (r : ℚ) + 1) - 1 / ((r : ℚ) + 1) = alpha r := by
  have hr1 : (r : ℚ) + 1 ≠ 0 := by positivity
  have hr2 : 2 * (r : ℚ) + 1 ≠ 0 := by positivity
  rw [alpha]
  field_simp
  ring

/-- Exact evaluation of the first thirteen row masses. -/
theorem A13_eq :
    A13 = 2014819799 / 5736673800 := by
  norm_num [A13, alpha, Finset.sum_Icc_succ_top]

/-- Exact evaluation of the nine small-prime capacities. -/
theorem S23_eq :
    S23 = 17927 / 7920 := by
  norm_num [S23, smallPrimes]

/-- Exact rational evaluation of `C0`. -/
theorem C0Rat_eq :
    C0Rat = 4029639598 / 25970038185 := by
  rw [C0Rat, A13_eq, S23_eq]
  norm_num



/-- The rational constant in this file is exactly the real constant fixed in
`Definitions.lean`. -/
theorem C0_eq_ratCast_C0Rat :
    C0 = (C0Rat : ℝ) := by
  rw [C0Rat_eq]
  norm_num [C0]



theorem three_div_twenty_five_lt_C0Rat :
    (3 : ℚ) / 25 < C0Rat := by
  rw [C0Rat_eq]
  norm_num







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.StationaryLayers -/
section


/-!
# Stationary prime layers

For a fixed row `r`, Section 3 uses the prime interval
`n / (r + 1) < p ≤ 2n / (2r + 1)`.  The definition below records the
endpoints by cross-multiplied natural-number inequalities, so there is no
rounding ambiguity.  Its cardinality is then identified with the exact
prime-counting difference to which the fixed-interval PNT applies.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section



@[simp]
theorem mem_stationaryPrimeLayer {n r p : ℕ} :
    p ∈ stationaryPrimeLayer n r ↔
      p.Prime ∧ n < p * (r + 1) ∧ p * (2 * r + 1) ≤ 2 * n := by
  simp only [stationaryPrimeLayer, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun hp ↦ hp.2
  · intro hp
    have hpLe : p ≤ 2 * n :=
      (Nat.le_mul_of_pos_right p (by omega : 0 < 2 * r + 1)).trans hp.2.2
    exact ⟨by omega, hp⟩



private theorem stationaryPrimeLayer_eq_filter_Ioc (n r : ℕ) :
    stationaryPrimeLayer n r =
      (Finset.Ioc (n / (r + 1)) ((2 * n) / (2 * r + 1))).filter Nat.Prime := by
  ext p
  simp only [mem_stationaryPrimeLayer, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    exact ⟨⟨(Nat.div_lt_iff_lt_mul (by omega)).2 hpLower,
      (Nat.le_div_iff_mul_le (by omega)).2 hpUpper⟩, hpPrime⟩
  · rintro ⟨⟨hpLower, hpUpper⟩, hpPrime⟩
    exact ⟨hpPrime, (Nat.div_lt_iff_lt_mul (by omega)).1 hpLower,
      (Nat.le_div_iff_mul_le (by omega)).1 hpUpper⟩

private theorem card_filter_prime_Ioc {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card =
      Nat.primeCounting b - Nat.primeCounting a := by
  classical
  have hdiff :
      (Finset.Ioc a b).filter Nat.Prime =
        (Finset.range (b + 1)).filter Nat.Prime \
          (Finset.range (a + 1)).filter Nat.Prime := by
    ext p
    by_cases hp : p.Prime
    · simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
        Finset.mem_range, hp, and_true]
      omega
    · simp [hp]
  have hsubset :
      (Finset.range (a + 1)).filter Nat.Prime ⊆
        (Finset.range (b + 1)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1.trans_le (Nat.add_le_add_right hab 1), hp.2⟩
  rw [hdiff, Finset.card_sdiff_of_subset hsubset]
  simp only [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

private theorem stationary_lower_natFloor (n r : ℕ) :
    ⌊((1 : ℝ) / ((r : ℝ) + 1)) * (n : ℝ)⌋₊ = n / (r + 1) := by
  have harg :
      ((1 : ℝ) / ((r : ℝ) + 1)) * (n : ℝ) =
        (n : ℝ) / ((r + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [harg]
  exact Nat.floor_div_eq_div n (r + 1)

private theorem stationary_upper_natFloor (n r : ℕ) :
    ⌊((2 : ℝ) / (2 * (r : ℝ) + 1)) * (n : ℝ)⌋₊ =
      (2 * n) / (2 * r + 1) := by
  have harg :
      ((2 : ℝ) / (2 * (r : ℝ) + 1)) * (n : ℝ) =
        ((2 * n : ℕ) : ℝ) / ((2 * r + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [harg]
  exact Nat.floor_div_eq_div (2 * n) (2 * r + 1)

private theorem stationary_endpoint_le (r : ℕ) :
    (1 : ℝ) / ((r : ℝ) + 1) ≤
      2 / (2 * (r : ℝ) + 1) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

/-- Exact cardinality of a stationary layer as a difference of prime-counting
functions at the two floored endpoints. -/
theorem stationaryPrimeLayer_card (n r : ℕ) :
    (stationaryPrimeLayer n r).card =
      Nat.primeCounting
          ⌊((2 : ℝ) / (2 * (r : ℝ) + 1)) * (n : ℝ)⌋₊ -
        Nat.primeCounting
          ⌊((1 : ℝ) / ((r : ℝ) + 1)) * (n : ℝ)⌋₊ := by
  have hfloor :
      ⌊((1 : ℝ) / ((r : ℝ) + 1)) * (n : ℝ)⌋₊ ≤
        ⌊((2 : ℝ) / (2 * (r : ℝ) + 1)) * (n : ℝ)⌋₊ :=
    Nat.floor_mono
      (mul_le_mul_of_nonneg_right (stationary_endpoint_le r) (Nat.cast_nonneg n))
  rw [stationaryPrimeLayer_eq_filter_Ioc]
  rw [stationary_lower_natFloor, stationary_upper_natFloor] at hfloor ⊢
  exact card_filter_prime_Ioc hfloor

/-- For every fixed paper row `r ≥ 1`, the stationary layer has asymptotic
mass `alpha r` after normalization by `n / log n`. -/
theorem stationaryPrimeLayer_card_normalized_tendsto (r : ℕ) (_hr : 1 ≤ r) :
    Tendsto
      (fun n : ℕ ↦
        ((stationaryPrimeLayer n r).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (alpha r : ℝ)) := by
  have ha : 0 < (1 : ℝ) / ((r : ℝ) + 1) := by positivity
  have hinterval :=
    SafePrimeCounting.primeCounting_interval_natSub_normalized_tendsto
      (a := (1 : ℝ) / ((r : ℝ) + 1))
      (b := (2 : ℝ) / (2 * (r : ℝ) + 1))
      ha (stationary_endpoint_le r)
  have halpha :
      (2 : ℝ) / (2 * (r : ℝ) + 1) -
          1 / ((r : ℝ) + 1) =
        (alpha r : ℝ) := by
    simpa using
      congrArg (fun q : ℚ ↦ (q : ℝ)) (two_div_sub_one_div_eq_alpha r)
  simpa only [stationaryPrimeLayer_card, halpha] using hinterval

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralExtension -/
section


/-!
# Extension to the central binomial endpoint

This is the exact preliminary construction in the first lower-bound lemma:
a complement representation ending at `M ≤ 2n` is extended by every integer
in `(M,2n]`, producing a distinct-factor representation of `choose (2n) n`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section









theorem centralChoose_mul_factorial_sq (n : ℕ) :
    Nat.choose (2 * n) n * n.factorial ^ 2 = (2 * n).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  have hsub : 2 * n - n = n := by omega
  simpa [hsub, pow_two, mul_assoc] using h







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TailValuationCore -/
section


/-! # Per-prime factorial-tail valuation estimates -/

namespace Erdos390.WholePaper

noncomputable section

theorem factorialValuation_eq_choose_add_factorialValuation_add
    {a h p : ℕ} :
    (a + h).factorial.factorization p =
      (Nat.choose (a + h) h).factorization p +
        h.factorial.factorization p + a.factorial.factorization p := by
  have hchoosePos : 0 < Nat.choose (a + h) h :=
    Nat.choose_pos (Nat.le_add_left h a)
  have hfactorization := congrArg Nat.factorization
    (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left h a))
  simp only [Nat.add_sub_cancel_right] at hfactorization
  rw [Nat.factorization_mul
      (mul_ne_zero hchoosePos.ne' (Nat.factorial_ne_zero h))
      (Nat.factorial_ne_zero a),
    Nat.factorization_mul hchoosePos.ne' (Nat.factorial_ne_zero h)] at hfactorization
  have hcoordinate := congrArg (fun v : ℕ →₀ ℕ ↦ v p) hfactorization
  simpa only [Finsupp.add_apply] using hcoordinate.symm

theorem factorialValuationSub_eq_choose_add_factorialValuation
    {a h p : ℕ} :
    (a + h).factorial.factorization p - a.factorial.factorization p =
      (Nat.choose (a + h) h).factorization p + h.factorial.factorization p := by
  rw [factorialValuation_eq_choose_add_factorialValuation_add]
  omega

theorem factorialValuationSub_le_div_pred_add_log2
    {a h p : ℕ} (hp : p.Prime) :
    (a + h).factorial.factorization p - a.factorial.factorization p ≤
      h / (p - 1) + Nat.log2 (a + h) := by
  rw [factorialValuationSub_eq_choose_add_factorialValuation]
  have hchoose :
      (Nat.choose (a + h) h).factorization p ≤ Nat.log2 (a + h) := by
    calc
      (Nat.choose (a + h) h).factorization p ≤ Nat.log p (a + h) :=
        Nat.factorization_choose_le_log
      _ ≤ Nat.log 2 (a + h) :=
        Nat.log_anti_left Nat.one_lt_two hp.two_le
      _ = Nat.log2 (a + h) := Nat.log2_eq_log_two.symm
  have hfactorial :
      h.factorial.factorization p ≤ h / (p - 1) :=
    Nat.factorization_factorial_le_div_pred hp h
  omega

theorem centralFactorialValuation_eq_choose_add {n p : ℕ} :
    (2 * n).factorial.factorization p =
      (Nat.choose (2 * n) n).factorization p +
        2 * n.factorial.factorization p := by
  have hchoosePos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  have hfactorization := congrArg Nat.factorization
    (centralChoose_mul_factorial_sq n)
  rw [Nat.factorization_mul hchoosePos.ne'
      (pow_ne_zero 2 (Nat.factorial_ne_zero n)),
    Nat.factorization_pow] at hfactorization
  have hcoordinate := congrArg (fun v : ℕ →₀ ℕ ↦ v p) hfactorization
  simpa only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    Nat.cast_ofNat] using hcoordinate.symm







end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralPromotion -/
section


/-! # Promotion of residual central prime powers

This file formalizes the elementary promotion step from Section 10 of the
paper.  A positive block `B ≤ 2n` is multiplied by the least power of two
which puts it above `n`; the resulting block still lies at most `2n`.
-/

namespace Erdos390.WholePaper

noncomputable section





theorem promotionExponent_spec {n B : ℕ} (hB : 0 < B) :
    n < 2 ^ promotionExponent n B * B := by
  have htarget : n / B + 1 ≤ 2 ^ promotionExponent n B := by
    simpa only [promotionExponent] using
      Nat.le_pow_clog Nat.one_lt_two (n / B + 1)
  apply (Nat.div_lt_iff_lt_mul hB).mp
  omega

theorem promotionExponent_minimal {n B k : ℕ}
    (hk : k < promotionExponent n B) :
    2 ^ k * B ≤ n := by
  have hpow : 2 ^ k < n / B + 1 := by
    exact (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mp hk
  have hpow' : 2 ^ k ≤ n / B := by omega
  exact (Nat.mul_le_mul_right B hpow').trans (Nat.div_mul_le_self n B)

theorem promotedBlock_gt {n B : ℕ} (hB : 0 < B) :
    n < promotedBlock n B := by
  exact promotionExponent_spec hB

theorem promotedBlock_le_two_mul {n B : ℕ}
    (hB : 0 < B) (hBupper : B ≤ 2 * n) :
    promotedBlock n B ≤ 2 * n := by
  by_cases hBn : B ≤ n
  · have hdivPos : 0 < n / B := Nat.div_pos hBn hB
    have htarget : 1 < n / B + 1 := by omega
    have hkPos : 0 < promotionExponent n B := by
      simpa only [promotionExponent] using
        Nat.clog_pos Nat.one_lt_two htarget
    have hkPred : promotionExponent n B - 1 < promotionExponent n B := by
      omega
    have hprevious : 2 ^ (promotionExponent n B - 1) * B ≤ n :=
      promotionExponent_minimal hkPred
    have hkSplit : promotionExponent n B - 1 + 1 = promotionExponent n B := by
      omega
    rw [promotedBlock, ← hkSplit, pow_succ]
    calc
      (2 ^ (promotionExponent n B - 1) * 2) * B =
          2 * (2 ^ (promotionExponent n B - 1) * B) := by ac_rfl
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hprevious
  · have hnB : n < B := Nat.lt_of_not_ge hBn
    have hdiv : n / B = 0 := Nat.div_eq_of_lt hnB
    simp [promotedBlock, promotionExponent, hdiv, hBupper]

theorem promotedBlock_mem_centralInterval {n B : ℕ}
    (hB : 0 < B) (hBupper : B ≤ 2 * n) :
    promotedBlock n B ∈ Finset.Ioc n (2 * n) := by
  exact Finset.mem_Ioc.mpr
    ⟨promotedBlock_gt hB, promotedBlock_le_two_mul hB hBupper⟩





theorem centralPrimeBlock_pos (n p : ℕ) : 0 < centralPrimeBlock n p := by
  cases p with
  | zero => simp [centralPrimeBlock]
  | succ p =>
      simpa only [centralPrimeBlock] using
        (pow_pos (Nat.succ_pos p)
          ((Nat.choose (2 * n) n).factorization (p + 1)))

theorem centralPrimeBlock_le_two_mul {n p : ℕ} (hn : 0 < n) :
    centralPrimeBlock n p ≤ 2 * n := by
  simpa only [centralPrimeBlock] using
    (Nat.pow_factorization_choose_le
      (p := p) (n := 2 * n) (k := n) (by omega))







theorem promotedCentralFactor_mem_centralInterval {n p : ℕ} (hn : 0 < n) :
    promotedCentralFactor n p ∈ Finset.Ioc n (2 * n) := by
  exact promotedBlock_mem_centralInterval
    (centralPrimeBlock_pos n p) (centralPrimeBlock_le_two_mul hn)





/-- Promotion does not change the valuation at an odd base prime. -/
theorem promotedCentralFactor_factorization_odd
    {n p : ℕ} (hp : p.Prime) (hpOdd : p ≠ 2) :
    (promotedCentralFactor n p).factorization p =
      (Nat.choose (2 * n) n).factorization p := by
  have htwoPow : 2 ^ promotionExponent n (centralPrimeBlock n p) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hpPow : centralPrimeBlock n p ≠ 0 :=
    (centralPrimeBlock_pos n p).ne'
  have htwoPrime : Nat.Prime 2 := by norm_num
  have htwoFac :
      (2 ^ promotionExponent n (centralPrimeBlock n p)).factorization p = 0 := by
    rw [htwoPrime.factorization_pow]
    simp [Ne.symm hpOdd]
  rw [promotedCentralFactor, promotedBlock,
    Nat.factorization_mul htwoPow hpPow]
  simp only [Finsupp.add_apply]
  rw [htwoFac, centralPrimeBlock, Nat.factorization_pow_self hp]
  simp

/-- At an odd prime `p`, a promoted factor based at a different prime `q`
has zero `p`-valuation. -/
theorem promotedCentralFactor_factorization_cross
    {n p q : ℕ} (hq : q.Prime) (hpOdd : p ≠ 2) (hpq : p ≠ q) :
    (promotedCentralFactor n q).factorization p = 0 := by
  have htwoPow : 2 ^ promotionExponent n (centralPrimeBlock n q) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hqPow : centralPrimeBlock n q ≠ 0 :=
    (centralPrimeBlock_pos n q).ne'
  have htwoPrime : Nat.Prime 2 := by norm_num
  have htwoFac :
      (2 ^ promotionExponent n (centralPrimeBlock n q)).factorization p = 0 := by
    rw [htwoPrime.factorization_pow]
    simp [Ne.symm hpOdd]
  have hqFac : (centralPrimeBlock n q).factorization p = 0 := by
    rw [centralPrimeBlock, hq.factorization_pow]
    simp [Ne.symm hpq]
  rw [promotedCentralFactor, promotedBlock,
    Nat.factorization_mul htwoPow hqPow]
  simp only [Finsupp.add_apply]
  rw [htwoFac, hqFac, add_zero]



/-- Promoted factors attached to distinct primes with positive central
exponent are distinct. -/
theorem promotedCentralFactor_injective_on_positive_support
    {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpExponent : 0 < (Nat.choose (2 * n) n).factorization p)
    (hqExponent : 0 < (Nat.choose (2 * n) n).factorization q)
    (hfactor : promotedCentralFactor n p = promotedCentralFactor n q) :
    p = q := by
  by_contra hpq
  by_cases hpTwo : p = 2
  · have hqOdd : q ≠ 2 := by
      intro hqTwo
      apply hpq
      exact hpTwo.trans hqTwo.symm
    have hcoordinate := congrArg (fun a : ℕ ↦ a.factorization q) hfactor
    change (promotedCentralFactor n p).factorization q =
      (promotedCentralFactor n q).factorization q at hcoordinate
    rw [promotedCentralFactor_factorization_cross
        (p := q) (q := p) hp hqOdd (Ne.symm hpq),
      promotedCentralFactor_factorization_odd hq hqOdd] at hcoordinate
    omega
  · have hcoordinate := congrArg (fun a : ℕ ↦ a.factorization p) hfactor
    change (promotedCentralFactor n p).factorization p =
      (promotedCentralFactor n q).factorization p at hcoordinate
    rw [promotedCentralFactor_factorization_odd hp hpTwo,
      promotedCentralFactor_factorization_cross
        (p := p) (q := q) hq hpTwo hpq] at hcoordinate
    omega

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ResidualCentralFactors -/
section


/-! # The finite family of promoted residual central factors -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section









theorem residualCentralPrimes_le {n X p : ℕ}
    (hp : p ∈ residualCentralPrimes n X) : p ≤ X :=
  (Finset.mem_filter.mp hp).2

theorem residualCentralPrimes_exponent_pos {n X p : ℕ}
    (hp : p ∈ residualCentralPrimes n X) :
    0 < (Nat.choose (2 * n) n).factorization p := by
  have hpMem : p ∈ (Nat.choose (2 * n) n).primeFactors :=
    (Finset.mem_filter.mp hp).1
  have hchoosePos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  exact (Nat.prime_of_mem_primeFactors hpMem).factorization_pos_of_dvd
    hchoosePos.ne' (Nat.dvd_of_mem_primeFactors hpMem)

theorem promotedCentralFactor_injOn_residualCentralPrimes (n X : ℕ) :
    Set.InjOn (promotedCentralFactor n) (residualCentralPrimes n X) := by
  intro p hp q hq hpq
  exact promotedCentralFactor_injective_on_positive_support
    (residualCentralPrimes_prime hp) (residualCentralPrimes_prime hq)
    (residualCentralPrimes_exponent_pos hp)
    (residualCentralPrimes_exponent_pos hq) hpq



theorem residualPromotedFactors_subset_centralInterval
    {n X : ℕ} (hn : 0 < n) :
    residualPromotedFactors n X ⊆ Finset.Ioc n (2 * n) := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  exact promotedCentralFactor_mem_centralInterval hn

/-- Exact product identity for the promoted residual family. -/
theorem residualPromotedFactors_prod (n X : ℕ) :
    (residualPromotedFactors n X).prod id =
      2 ^ residualPromotionCost n X *
        (residualCentralPrimes n X).prod (centralPrimeBlock n) := by
  rw [residualPromotedFactors,
    Finset.prod_image
      (promotedCentralFactor_injOn_residualCentralPrimes n X)]
  simp only [id_eq, promotedCentralFactor, promotedBlock]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralPrimeBlockDecomposition -/
section


/-!
# Exact low/high decomposition of the central binomial coefficient

The central binomial coefficient is the product of its complete prime-power
blocks.  Splitting those blocks at the anchor cutoff and promoting every low
block therefore introduces exactly one aggregate power of two and no other
valuation error.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



theorem largeCentralPrimes_prime {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : p.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem largeCentralPrimes_gt {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : X < p :=
  (Finset.mem_filter.mp hp).2

theorem residualCentralPrimes_disjoint_largeCentralPrimes (n X : ℕ) :
    Disjoint (residualCentralPrimes n X) (largeCentralPrimes n X) := by
  rw [Finset.disjoint_left]
  intro p hpLow hpHigh
  exact (not_lt_of_ge (residualCentralPrimes_le hpLow))
    (largeCentralPrimes_gt hpHigh)

theorem residualCentralPrimes_union_largeCentralPrimes (n X : ℕ) :
    residualCentralPrimes n X ∪ largeCentralPrimes n X =
      (Nat.choose (2 * n) n).primeFactors := by
  ext p
  simp only [residualCentralPrimes, largeCentralPrimes,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  · intro hp
    by_cases hle : p ≤ X
    · exact Or.inl ⟨hp, hle⟩
    · exact Or.inr ⟨hp, by omega⟩

/-- The product of all complete central prime-power blocks is exactly the
central binomial coefficient. -/
theorem centralPrimeBlocks_prod_all (n : ℕ) :
    ((Nat.choose (2 * n) n).primeFactors).prod (centralPrimeBlock n) =
      Nat.choose (2 * n) n := by
  have hchoose : Nat.choose (2 * n) n ≠ 0 :=
    (Nat.choose_pos (by omega)).ne'
  simpa only [centralPrimeBlock, Nat.support_factorization] using
    Nat.factorization_prod_pow_eq_self hchoose

/-- Exact multiplicative split at an arbitrary cutoff. -/
theorem residual_mul_largeCentralPrimeBlocks (n X : ℕ) :
    (residualCentralPrimes n X).prod (centralPrimeBlock n) *
        (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      Nat.choose (2 * n) n := by
  rw [← Finset.prod_union
    (residualCentralPrimes_disjoint_largeCentralPrimes n X),
    residualCentralPrimes_union_largeCentralPrimes,
    centralPrimeBlocks_prod_all]

/-- Promoting all low blocks changes the complete central product by exactly
`2^K` and leaves the high blocks untouched. -/
theorem residualPromoted_mul_largeCentralPrimeBlocks (n X : ℕ) :
    (residualPromotedFactors n X).prod id *
        (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      2 ^ residualPromotionCost n X * Nat.choose (2 * n) n := by
  rw [residualPromotedFactors_prod]
  calc
    (2 ^ residualPromotionCost n X *
          (residualCentralPrimes n X).prod (centralPrimeBlock n)) *
        (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      2 ^ residualPromotionCost n X *
        ((residualCentralPrimes n X).prod (centralPrimeBlock n) *
          (largeCentralPrimes n X).prod (centralPrimeBlock n)) := by
        ac_rfl
    _ = 2 ^ residualPromotionCost n X * Nat.choose (2 * n) n := by
      rw [residual_mul_largeCentralPrimeBlocks]

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralCarryAnchors -/
section


/-! # Exact arithmetic of the fixed-prefix central carry anchors -/

namespace Erdos390.WholePaper

noncomputable section

/-- A stationary-layer prime has the two exact floor values displayed in
the paper. -/
theorem stationaryPrimeLayer_floor_values {n r p : ℕ}
    (hp : p ∈ stationaryPrimeLayer n r) :
    n / p = r ∧ (2 * n) / p = 2 * r + 1 := by
  have hmem := mem_stationaryPrimeLayer.mp hp
  have hpPos : 0 < p := hmem.1.pos
  have hrp : r * p ≤ n := by
    have hupper := hmem.2.2
    ring_nf at hupper ⊢
    omega
  have htwoStrict : 2 * n < (2 * r + 2) * p := by
    have hlower := hmem.2.1
    ring_nf at hlower ⊢
    omega
  constructor
  · apply Nat.le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpPos).2 (by
        simpa [Nat.mul_comm] using hmem.2.1))
    · exact (Nat.le_div_iff_mul_le hpPos).2 hrp
  · apply Nat.le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpPos).2 (by
        simpa [Nat.mul_comm] using htwoStrict))
    · exact (Nat.le_div_iff_mul_le hpPos).2 (by
        simpa [Nat.mul_comm] using hmem.2.2)

/-- Above the square-root cutoff, a stationary-layer prime occurs exactly
once in the central binomial coefficient. -/
theorem centralChoose_factorization_eq_one_of_mem_stationaryPrimeLayer_of_sq
    {n r p : ℕ} (hn : 0 < n)
    (hp : p ∈ stationaryPrimeLayer n r) (hpSq : 2 * n < p ^ 2) :
    (Nat.choose (2 * n) n).factorization p = 1 := by
  have hpPrime : p.Prime := (mem_stationaryPrimeLayer.mp hp).1
  have hfloors := stationaryPrimeLayer_floor_values hp
  have hnSq : n < p ^ 2 := by omega
  have hnFac : n.factorial.factorization p = r := by
    rw [factorial_factorization_eq_div_of_lt_sq hpPrime hn hnSq,
      hfloors.1]
  have htwoFac : (2 * n).factorial.factorization p = 2 * r + 1 := by
    rw [factorial_factorization_eq_div_of_lt_sq hpPrime (by omega) hpSq,
      hfloors.2]
  have hcentral := centralFactorialValuation_eq_choose_add
    (n := n) (p := p)
  rw [hnFac, htwoFac] at hcentral
  omega

/-- Every allowed allocation cofactor places its carry prime anchor in the
central interval. -/
theorem stationaryPrimeLayer_mul_cofactor_mem_centralInterval
    {n r p q : ℕ} (hp : p ∈ stationaryPrimeLayer n r)
    (hqLower : r + 1 ≤ q) (hqUpper : q ≤ 2 * r + 1) :
    p * q ∈ Finset.Ioc n (2 * n) := by
  have hmem := mem_stationaryPrimeLayer.mp hp
  apply Finset.mem_Ioc.mpr
  constructor
  · exact hmem.2.1.trans_le (Nat.mul_le_mul_left p hqLower)
  · exact (Nat.mul_le_mul_left p hqUpper).trans hmem.2.2



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.LargeCentralPrimeRouting -/
section


/-!
# Routing every large central prime to a carry row or row zero

Above a square-root cutoff, Legendre's formula has only its first term.
Thus every large prime divisor of the central binomial coefficient occurs
once, and its quotient row `n / p` determines its unique anchor family.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- If a prime occurs in the central binomial coefficient and `p^2 > 2n`,
then its valuation is one and the two floor quotients differ by one carry. -/
theorem centralChoose_largePrime_carry
    {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpExponent : 0 < (Nat.choose (2 * n) n).factorization p)
    (hpSq : 2 * n < p ^ 2) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      (2 * n) / p = 2 * (n / p) + 1 := by
  let r := n / p
  have hnSq : n < p ^ 2 := by omega
  have hnFac : n.factorial.factorization p = r := by
    simpa only [r] using
      factorial_factorization_eq_div_of_lt_sq hp hn hnSq
  have htwoFac : (2 * n).factorial.factorization p = (2 * n) / p := by
    exact factorial_factorization_eq_div_of_lt_sq hp (by omega) hpSq
  have hnUpper : n < p * (r + 1) := by
    simpa only [r] using Nat.lt_mul_div_succ n hp.pos
  have htwoUpper : 2 * n < (2 * r + 2) * p := by
    calc
      2 * n < 2 * (p * (r + 1)) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
      _ = (2 * r + 2) * p := by ring
  have hdivUpper : (2 * n) / p ≤ 2 * r + 1 := by
    have hlt : (2 * n) / p < 2 * r + 2 :=
      (Nat.div_lt_iff_lt_mul hp.pos).2 htwoUpper
    omega
  have hcentral := centralFactorialValuation_eq_choose_add
    (n := n) (p := p)
  rw [hnFac, htwoFac] at hcentral
  constructor <;> omega

/-- A cutoff strictly below `p` transfers its square bound to `p`. -/
theorem two_mul_lt_prime_sq_of_cutoff
    {n X p : ℕ} (hXsq : 2 * n < X ^ 2) (hXp : X < p) :
    2 * n < p ^ 2 := by
  have hPow : X ^ 2 < p ^ 2 := by
    rw [pow_two, pow_two]
    exact (Nat.mul_le_mul_left X hXp.le).trans_lt
      ((Nat.mul_lt_mul_right (by omega : 0 < p)).2 hXp)
  exact hXsq.trans hPow

/-- Every large central prime is routed exactly either to the row-zero
interval `(n,2n]` or to its positive stationary carry row. -/
theorem largeCentralPrime_rowZero_or_stationary
    {n X p : ℕ} (hn : 0 < n) (hXsq : 2 * n < X ^ 2)
    (hpMem : p ∈ largeCentralPrimes n X) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      ((n < p ∧ p ≤ 2 * n) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r) := by
  have hpPrime := largeCentralPrimes_prime hpMem
  have hpFactors : p ∈ (Nat.choose (2 * n) n).primeFactors :=
    (Finset.mem_filter.mp hpMem).1
  have hpExponent : 0 < (Nat.choose (2 * n) n).factorization p := by
    exact hpPrime.factorization_pos_of_dvd
      (Nat.choose_pos (by omega)).ne'
      (Nat.dvd_of_mem_primeFactors hpFactors)
  have hpSq := two_mul_lt_prime_sq_of_cutoff hXsq
    (largeCentralPrimes_gt hpMem)
  obtain ⟨hpOne, hfloor⟩ :=
    centralChoose_largePrime_carry hn hpPrime hpExponent hpSq
  refine ⟨hpOne, ?_⟩
  let r := n / p
  have hnUpper : n < p * (r + 1) := by
    simpa only [r] using Nat.lt_mul_div_succ n hpPrime.pos
  by_cases hrZero : r = 0
  · left
    constructor
    · simpa only [hrZero, zero_add, mul_one] using hnUpper
    · have hOneLe : 1 ≤ (2 * n) / p := by
        rw [hfloor]
        omega
      have hpLe := (Nat.le_div_iff_mul_le hpPrime.pos).1 hOneLe
      simpa only [one_mul] using hpLe
  · right
    refine ⟨r, Nat.one_le_iff_ne_zero.mpr hrZero, rfl, ?_⟩
    rw [mem_stationaryPrimeLayer]
    refine ⟨hpPrime, hnUpper, ?_⟩
    have hrowLe : 2 * r + 1 ≤ (2 * n) / p := by omega
    have hmul := (Nat.le_div_iff_mul_le hpPrime.pos).1 hrowLe
    simpa only [Nat.mul_comm] using hmul

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorCollision -/
section


/-!
# Collision guards for the three central-anchor families

The prefix and row-zero anchors carry a marker prime above a fixed cutoff.
Every promoted residual factor is supported only at `2` and its base prime,
both below that cutoff.  The lemmas below turn this unique-factorization
observation into literal natural-number noncollision statements.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- A prime divisor of `A_p = 2^k p^e` is either `2` or the base prime
`p`. -/
theorem prime_dvd_promotedCentralFactor
    {n p ℓ : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime)
    (hdiv : ℓ ∣ promotedCentralFactor n p) :
    ℓ = 2 ∨ ℓ = p := by
  rw [promotedCentralFactor, promotedBlock, centralPrimeBlock] at hdiv
  rcases hℓ.dvd_mul.mp hdiv with htwo | hpPow
  · left
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
      (hℓ.dvd_of_dvd_pow htwo)
  · right
    exact (Nat.prime_dvd_prime_iff_eq hℓ hp).mp
      (hℓ.dvd_of_dvd_pow hpPow)

/-- A marker prime above `X` cannot divide a promoted factor whose base
prime is at most `X`, provided `2 ≤ X`. -/
theorem markerPrime_not_dvd_promotedCentralFactor
    {n X P p : ℕ} (hP : P.Prime) (hp : p.Prime)
    (hXTwo : 2 ≤ X) (hPLarge : X < P) (hpSmall : p ≤ X) :
    ¬ P ∣ promotedCentralFactor n p := by
  intro hdiv
  rcases prime_dvd_promotedCentralFactor hp hP hdiv with hP2 | hPp
  · omega
  · omega

/-- No prefix-style marker--cofactor product can collide with a promoted
residual factor. -/
theorem marker_mul_ne_promotedCentralFactor
    {n X P q p : ℕ} (hP : P.Prime) (hp : p.Prime)
    (hXTwo : 2 ≤ X) (hPLarge : X < P) (hpSmall : p ≤ X) :
    P * q ≠ promotedCentralFactor n p := by
  intro heq
  apply markerPrime_not_dvd_promotedCentralFactor hP hp hXTwo hPLarge hpSmall
  rw [← heq]
  exact dvd_mul_right P q





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorProduct -/
section


/-!
# Exact product of all three central-anchor families

This file isolates the finite algebra behind the full central-anchor lemma.
For every large central prime, a cofactor choice is required to follow either
its row-zero route or its stationary carry row.  The resulting marker factors
are combined with every promoted low prime-power block.  Their product is
proved to be the central binomial coefficient times the literal cofactor and
promotion divisor.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section







theorem routedCentralCofactor_mem_centralInterval
    {n p q : ℕ} (hq : IsRoutedCentralCofactor n p q) :
    p * q ∈ Finset.Ioc n (2 * n) := by
  rcases hq with hzero | ⟨r, _hrPos, _hr, hpRow, hqLower, hqUpper⟩
  · simpa only [hzero.2.2, mul_one] using
      (show p ∈ Finset.Ioc n (2 * n) from
        Finset.mem_Ioc.mpr ⟨hzero.1, hzero.2.1⟩)
  · exact stationaryPrimeLayer_mul_cofactor_mem_centralInterval
      hpRow hqLower hqUpper









theorem largeCentralAnchor_mem_centralInterval
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n X) :
    largeCentralAnchor q p ∈ Finset.Ioc n (2 * n) := by
  exact routedCentralCofactor_mem_centralInterval (hq p hp)

/-- The square separation prevents two different large marker primes from
occurring in the same central-interval integer. -/
theorem largeCentralAnchor_injOn
    {n X : ℕ} {q : ℕ → ℕ} (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q) :
    Set.InjOn (largeCentralAnchor q) (largeCentralPrimes n X) := by
  intro p hp p' hp' heq
  by_contra hpp'
  have hpPrime := largeCentralPrimes_prime hp
  have hp'Prime := largeCentralPrimes_prime hp'
  have haMem := largeCentralAnchor_mem_centralInterval hq hp
  have haPos : 0 < largeCentralAnchor q p := by
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp haMem).1
  have haUpper : largeCentralAnchor q p ≤ 2 * n :=
    (Finset.mem_Ioc.mp haMem).2
  apply not_two_distinct_large_primes_dvd
    hpPrime hp'Prime hpp'
    (largeCentralPrimes_gt hp).le (largeCentralPrimes_gt hp').le
    haPos haUpper (by simpa only [pow_two] using hXsq)
  constructor
  · exact dvd_mul_right p (q p)
  · rw [heq]
    exact dvd_mul_right p' (q p')

theorem largeCentralAnchors_subset_centralInterval
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    largeCentralAnchors n X q ⊆ Finset.Ioc n (2 * n) := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  exact largeCentralAnchor_mem_centralInterval hq hp



theorem largeCentralAnchors_prod
    {n X : ℕ} {q : ℕ → ℕ} (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q) :
    (largeCentralAnchors n X q).prod id =
      (largeCentralPrimes n X).prod id *
        largeCentralCofactorProduct n X q := by
  rw [largeCentralAnchors,
    Finset.prod_image (largeCentralAnchor_injOn hXsq hq)]
  simp only [id_eq, largeCentralAnchor, largeCentralCofactorProduct,
    Finset.prod_mul_distrib]

theorem largeCentralPrimeBlocks_eq_primeProduct
    {n X : ℕ} (hn : 0 < n) (hXsq : 2 * n < X ^ 2) :
    (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      (largeCentralPrimes n X).prod id := by
  apply Finset.prod_congr rfl
  intro p hp
  have hpOne :=
    (largeCentralPrime_rowZero_or_stationary hn hXsq hp).1
  simp only [centralPrimeBlock, hpOne, pow_one, id_eq]





theorem residualPromotedFactors_disjoint_largeCentralAnchors
    {n X : ℕ} {q : ℕ → ℕ} (hXTwo : 2 ≤ X) :
    Disjoint (residualPromotedFactors n X)
      (largeCentralAnchors n X q) := by
  rw [Finset.disjoint_left]
  intro a haLow haHigh
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp haLow
  obtain ⟨P, hP, hEq⟩ := Finset.mem_image.mp haHigh
  have hpPrime := residualCentralPrimes_prime hp
  have hPPrime := largeCentralPrimes_prime hP
  apply marker_mul_ne_promotedCentralFactor
    hPPrime hpPrime hXTwo (largeCentralPrimes_gt hP)
      (residualCentralPrimes_le hp)
  simpa only [largeCentralAnchor] using hEq

theorem fullCentralAnchors_subset_centralInterval
    {n X : ℕ} {q : ℕ → ℕ} (hn : 0 < n)
    (hq : IsLargeCentralCofactorChoice n X q) :
    fullCentralAnchors n X q ⊆ Finset.Ioc n (2 * n) := by
  intro a ha
  rcases Finset.mem_union.mp ha with haLow | haHigh
  · exact residualPromotedFactors_subset_centralInterval hn haLow
  · exact largeCentralAnchors_subset_centralInterval hq haHigh



/-- Literal exact product identity for the complete central-anchor set. -/
theorem fullCentralAnchors_prod
    {n X : ℕ} {q : ℕ → ℕ} (hn : 0 < n) (hXTwo : 2 ≤ X)
    (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q) :
    (fullCentralAnchors n X q).prod id =
      Nat.choose (2 * n) n * centralAnchorDivisor n X q := by
  have hcentral := residualPromoted_mul_largeCentralPrimeBlocks n X
  rw [largeCentralPrimeBlocks_eq_primeProduct hn hXsq] at hcentral
  rw [fullCentralAnchors,
    Finset.prod_union
      (residualPromotedFactors_disjoint_largeCentralAnchors hXTwo),
    largeCentralAnchors_prod hXsq hq]
  calc
    (residualPromotedFactors n X).prod id *
        ((largeCentralPrimes n X).prod id *
          largeCentralCofactorProduct n X q) =
      ((residualPromotedFactors n X).prod id *
        (largeCentralPrimes n X).prod id) *
          largeCentralCofactorProduct n X q := by ac_rfl
    _ = (2 ^ residualPromotionCost n X * Nat.choose (2 * n) n) *
          largeCentralCofactorProduct n X q := by rw [hcentral]
    _ = Nat.choose (2 * n) n * centralAnchorDivisor n X q := by
      simp only [centralAnchorDivisor]
      ac_rfl

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorDivisorSupport -/
section


/-!
# Prime support and valuations of the central-anchor divisor

The exact anchor product introduces only the promotion power of two and the
chosen carry cofactors.  This file makes that assertion literal at every
prime, so later allocation estimates can be applied directly to the actual
integer divisor.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

theorem routedCentralCofactor_pos
    {n p q : ℕ} (hq : IsRoutedCentralCofactor n p q) : 0 < q := by
  rcases hq with hzero | ⟨r, _hrPos, _hr, _hpRow, hqLower, _hqUpper⟩
  · omega
  · omega

theorem largeCentralCofactor_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n X) :
    0 < q p :=
  routedCentralCofactor_pos (hq p hp)

theorem largeCentralCofactorProduct_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    0 < largeCentralCofactorProduct n X q := by
  exact Finset.prod_pos fun p hp ↦ largeCentralCofactor_pos hq hp

theorem centralAnchorDivisor_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    0 < centralAnchorDivisor n X q := by
  exact mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) _)
    (largeCentralCofactorProduct_pos hq)

/-- Every prime divisor is either the promotion prime `2` or divides one of
the literal chosen cofactors. -/
theorem prime_dvd_centralAnchorDivisor
    {n X ℓ : ℕ} {q : ℕ → ℕ} (hℓ : ℓ.Prime)
    (hdiv : ℓ ∣ centralAnchorDivisor n X q) :
    ℓ = 2 ∨ ∃ p ∈ largeCentralPrimes n X, ℓ ∣ q p := by
  rw [centralAnchorDivisor] at hdiv
  rcases hℓ.dvd_mul.mp hdiv with htwo | hcofactor
  · left
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
      (hℓ.dvd_of_dvd_pow htwo)
  · right
    simpa only [largeCentralCofactorProduct] using
      (hℓ.prime.dvd_finset_prod_iff q).mp hcofactor

/-- A uniform cofactor bound gives a literal finite prime support. -/
theorem prime_dvd_centralAnchorDivisor_le
    {n X B ℓ : ℕ} {q : ℕ → ℕ}
    (hqChoice : IsLargeCentralCofactorChoice n X q)
    (hqBound : ∀ p ∈ largeCentralPrimes n X, q p ≤ B)
    (hℓ : ℓ.Prime) (hdiv : ℓ ∣ centralAnchorDivisor n X q) :
    ℓ ≤ max 2 B := by
  rcases prime_dvd_centralAnchorDivisor hℓ hdiv with rfl | ⟨p, hp, hℓq⟩
  · exact le_max_left 2 B
  · have hℓLe : ℓ ≤ q p :=
      Nat.le_of_dvd (largeCentralCofactor_pos hqChoice hp) hℓq
    exact (hℓLe.trans (hqBound p hp)).trans (le_max_right 2 B)

/-- Exact valuation ledger: promotion contributes only at `2`, and every
other contribution is the sum of cofactor valuations. -/
theorem centralAnchorDivisor_factorization
    {n X ℓ : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    (centralAnchorDivisor n X q).factorization ℓ =
      (if ℓ = 2 then residualPromotionCost n X else 0) +
        ∑ p ∈ largeCentralPrimes n X, (q p).factorization ℓ := by
  have hcofactorNe : largeCentralCofactorProduct n X q ≠ 0 :=
    (largeCentralCofactorProduct_pos hq).ne'
  have hqNe : ∀ p ∈ largeCentralPrimes n X, q p ≠ 0 :=
    fun p hp ↦ (largeCentralCofactor_pos hq hp).ne'
  rw [centralAnchorDivisor,
    Nat.factorization_mul
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hcofactorNe]
  simp only [Finsupp.add_apply, largeCentralCofactorProduct]
  rw [Nat.factorization_prod_apply hqNe]
  by_cases hℓTwo : ℓ = 2
  · subst ℓ
    rw [Nat.factorization_pow_self Nat.prime_two]
    simp
  · have htwoFactorization :
        (2 ^ residualPromotionCost n X).factorization ℓ = 0 := by
      rw [Nat.prime_two.factorization_pow]
      simp [hℓTwo]
    rw [htwoFactorization, if_neg hℓTwo, zero_add]

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.TailValuationTwoSided -/
section


/-!
# Two-sided fixed-prime tail valuation bounds

The factorial quotient over `(a,a+h]` has `p`-valuation
`h/(p-1) + O(log(a+h))`.  This file records an exact integer version of
both sides.  The lower bound comes from Legendre's digit-sum identity and
is strong enough for the strict reserve in the central-anchor construction.
-/

namespace Erdos390.WholePaper

noncomputable section

private theorem digits_sum_le_pred_mul_length
    {p n : ℕ} (hp : p.Prime) :
    (p.digits n).sum ≤ (p - 1) * (p.digits n).length := by
  have listBound : ∀ l : List ℕ,
      (∀ d ∈ l, d < p) → l.sum ≤ (p - 1) * l.length := by
    intro l hd
    induction l with
    | nil => simp
    | cons d l ih =>
        have hdHead : d ≤ p - 1 := by
          have := hd d (by simp)
          omega
        have hdTail : ∀ e ∈ l, e < p := by
          intro e he
          exact hd e (by simp [he])
        have ih' := ih hdTail
        simp only [List.sum_cons, List.length_cons]
        calc
          d + l.sum ≤ (p - 1) + (p - 1) * l.length :=
            Nat.add_le_add hdHead ih'
          _ = (p - 1) * (l.length + 1) := by
            rw [Nat.mul_succ]
            omega
  exact listBound (p.digits n) (fun d hd ↦
    Nat.digits_lt_base hp.one_lt hd)

theorem digits_sum_le_pred_mul_log2_add_one
    {p n : ℕ} (hp : p.Prime) :
    (p.digits n).sum ≤ (p - 1) * (Nat.log2 n + 1) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hlength := digits_sum_le_pred_mul_length (n := n) hp
  rw [Nat.digits_len p n hp.one_lt hn] at hlength
  have hlog : Nat.log p n ≤ Nat.log 2 n :=
    Nat.log_anti_left Nat.one_lt_two hp.two_le
  rw [← Nat.log2_eq_log_two] at hlog
  exact hlength.trans (Nat.mul_le_mul_left (p - 1)
    (Nat.add_le_add_right hlog 1))

/-- Exact lower Legendre bound, written without integer division. -/
theorem factorialValuation_lower_cross
    {h p : ℕ} (hp : p.Prime) :
    h ≤ (p - 1) *
      (h.factorial.factorization p + Nat.log2 h + 1) := by
  have hdigitsLe : (p.digits h).sum ≤ h := Nat.digit_sum_le p h
  have hlegendre := Nat.sub_one_mul_factorization_factorial
    (n := h) hp
  have hrecover :
      (p - 1) * h.factorial.factorization p + (p.digits h).sum = h := by
    omega
  have hdigitsBound := digits_sum_le_pred_mul_log2_add_one
    (n := h) hp
  calc
    h = (p - 1) * h.factorial.factorization p +
        (p.digits h).sum := hrecover.symm
    _ ≤ (p - 1) * h.factorial.factorization p +
        (p - 1) * (Nat.log2 h + 1) :=
      Nat.add_le_add_left hdigitsBound _
    _ = (p - 1) *
        (h.factorial.factorization p + Nat.log2 h + 1) := by ring

/-- The interval `(a,a+h]` contains at least the valuation of `h!`, hence
inherits the exact lower Legendre bound. -/
theorem factorialValuationSub_lower_cross
    {a h p : ℕ} (hp : p.Prime) :
    h ≤ (p - 1) *
      ((a + h).factorial.factorization p - a.factorial.factorization p +
        Nat.log2 h + 1) := by
  have htail : h.factorial.factorization p ≤
      (a + h).factorial.factorization p - a.factorial.factorization p := by
    rw [factorialValuationSub_eq_choose_add_factorialValuation]
    omega
  exact (factorialValuation_lower_cross hp).trans
    (Nat.mul_le_mul_left (p - 1) (by omega))

/-- Exact two-sided version of
`v_p(∏_{a<j≤a+h} j) = h/(p-1) + O(log(a+h))`. -/
theorem factorialValuationSub_twoSided
    {a h p : ℕ} (hp : p.Prime) :
    h ≤ (p - 1) *
        ((a + h).factorial.factorization p - a.factorial.factorization p +
          Nat.log2 h + 1) ∧
      (a + h).factorial.factorization p - a.factorial.factorization p ≤
        h / (p - 1) + Nat.log2 (a + h) := by
  exact ⟨factorialValuationSub_lower_cross hp,
    factorialValuationSub_le_div_pred_add_log2 hp⟩

end

end Erdos390.WholePaper

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

/-- Hence the chosen tail length is eventually at most `n`. -/
theorem eventually_upperTailLength_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, upperTailLength c n ≤ n := by
  have hsmall := (upperTailLength_ratio_tendsto_zero hc).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hratio hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcast : (upperTailLength c n : ℝ) ≤ (n : ℝ) := by
    have hratioLe :
        (upperTailLength c n : ℝ) / (n : ℝ) ≤ 1 := hratio.le
    have := (div_le_iff₀ hnReal).mp hratioLe
    simpa only [one_mul] using this
  exact_mod_cast hcast



/-- A tail of length at most `n` gives an endpoint at most `3n`. -/
theorem upperEndpoint_le_three_mul {n h : ℕ} (hh : h ≤ n) :
    upperEndpoint n h ≤ 3 * n := by
  simp only [upperEndpoint]
  omega







private theorem log_sq_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

private theorem log_three_mul_natCast_mul_log_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.log (3 * (n : ℝ)) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hconstant :
      Tendsto (fun _n : ℕ ↦ Real.log 3) atTop (nhds (Real.log 3)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          Real.log 3 * (Real.log (n : ℝ) / (n : ℝ)) +
            Real.log (n : ℝ) ^ 2 / (n : ℝ))
        atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hconstant.mul log_natCast_div_natCast_tendsto_zero).add
        log_sq_natCast_div_natCast_tendsto_zero
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hnReal]
  ring

private theorem logb_two_three_mul_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.logb 2 (3 * (n : ℝ)) / secondOrderScale n)
      atTop (nhds 0) := by
  have hscaled :
      Tendsto
        (fun n : ℕ ↦
          (1 / Real.log 2) *
            (Real.log (3 * (n : ℝ)) * Real.log (n : ℝ) /
              (n : ℝ)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      log_three_mul_natCast_mul_log_div_natCast_tendsto_zero.const_mul
        (1 / Real.log 2)
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlogN : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos one_lt_two).ne'
  rw [Real.logb, secondOrderScale]
  field_simp

/-- The binary-logarithmic tail error is negligible on the second-order
scale. -/
theorem log2_three_mul_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (Nat.log2 (3 * n) : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    logb_two_three_mul_normalized_tendsto_zero
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (by positivity) (secondOrderScale_pos hn).le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hlogBound :
        (Nat.log2 (3 * n) : ℝ) ≤ Real.logb 2 (3 * (n : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        Real.log2_le_logb (3 * n)
    exact div_le_div_of_nonneg_right hlogBound
      (secondOrderScale_pos hn).le

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.UpperTailValuationAsymptotic -/
section


/-!
# Fixed-prime upper-tail valuation asymptotics

The paper's tail has length `ceil (c n / log n)` above `2n`.  The exact
integer two-sided Legendre bounds squeeze its valuation at every fixed prime.
The logarithmic remainder is discharged by `UpperScale`; no valuation limit
is assumed as an input.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section



/-- Real-cast form of the exact integer squeeze, with one common logarithmic
error valid whenever the tail length is at most `n`. -/
theorem upperTailValuation_cast_bounds
    {c : ℝ} {n p : ℕ} (hp : p.Prime)
    (htail : upperTailLength c n ≤ n) :
    (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) -
          ((Nat.log2 (3 * n) : ℝ) + 1) ≤
        (upperTailValuation c n p : ℝ) ∧
      (upperTailValuation c n p : ℝ) ≤
        (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) +
          ((Nat.log2 (3 * n) : ℝ) + 1) := by
  have htwo := factorialValuationSub_twoSided
    (a := 2 * n) (h := upperTailLength c n) (p := p) hp
  have hlowerNat :
      upperTailLength c n ≤ (p - 1) *
        (upperTailValuation c n p +
          Nat.log2 (upperTailLength c n) + 1) := by
    simpa only [upperTailValuation, upperEndpoint] using htwo.1
  have hupperNat :
      upperTailValuation c n p ≤
        upperTailLength c n / (p - 1) +
          Nat.log2 (upperEndpoint n (upperTailLength c n)) := by
    simpa only [upperTailValuation, upperEndpoint] using htwo.2
  have htailThree : upperTailLength c n ≤ 3 * n := by
    omega
  have hendpointThree :
      upperEndpoint n (upperTailLength c n) ≤ 3 * n :=
    upperEndpoint_le_three_mul htail
  have hlogTail :
      Nat.log2 (upperTailLength c n) ≤ Nat.log2 (3 * n) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right htailThree
  have hlogEndpoint :
      Nat.log2 (upperEndpoint n (upperTailLength c n)) ≤
        Nat.log2 (3 * n) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right hendpointThree
  have hpredPosNat : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hpredPos : 0 < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpredPosNat
  have hlowerCast :
      (upperTailLength c n : ℝ) ≤ ((p - 1 : ℕ) : ℝ) *
        ((upperTailValuation c n p : ℝ) +
          (Nat.log2 (upperTailLength c n) : ℝ) + 1) := by
    exact_mod_cast hlowerNat
  have hbaseLower :
      (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
        (upperTailValuation c n p : ℝ) +
          (Nat.log2 (upperTailLength c n) : ℝ) + 1 := by
    apply (div_le_iff₀ hpredPos).2
    simpa only [mul_comm] using hlowerCast
  have hlogTailCast :
      (Nat.log2 (upperTailLength c n) : ℝ) ≤
        (Nat.log2 (3 * n) : ℝ) := by
    exact_mod_cast hlogTail
  have hupperCast :
      (upperTailValuation c n p : ℝ) ≤
        (upperTailLength c n / (p - 1) : ℕ) +
          (Nat.log2 (upperEndpoint n (upperTailLength c n)) : ℝ) := by
    exact_mod_cast hupperNat
  have hdivCast :
      ((upperTailLength c n / (p - 1) : ℕ) : ℝ) ≤
        (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hlogEndpointCast :
      (Nat.log2 (upperEndpoint n (upperTailLength c n)) : ℝ) ≤
        (Nat.log2 (3 * n) : ℝ) := by
    exact_mod_cast hlogEndpoint
  constructor <;> linarith

/-- Divide the finite squeeze by a positive second-order scale. -/
theorem upperTailValuation_normalized_bounds
    {c : ℝ} {n p : ℕ} (hp : p.Prime)
    (htail : upperTailLength c n ≤ n)
    (hscale : 0 < secondOrderScale n) :
    (upperTailLength c n : ℝ) / secondOrderScale n /
          ((p - 1 : ℕ) : ℝ) -
        ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n ≤
      (upperTailValuation c n p : ℝ) / secondOrderScale n ∧
    (upperTailValuation c n p : ℝ) / secondOrderScale n ≤
      (upperTailLength c n : ℝ) / secondOrderScale n /
          ((p - 1 : ℕ) : ℝ) +
        ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n := by
  have hbounds := upperTailValuation_cast_bounds hp htail
  have hpredPos : 0 < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  constructor
  · calc
      (upperTailLength c n : ℝ) / secondOrderScale n /
            ((p - 1 : ℕ) : ℝ) -
          ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n =
        ((upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) -
            ((Nat.log2 (3 * n) : ℝ) + 1)) /
          secondOrderScale n := by
            field_simp [hscale.ne', hpredPos.ne']
      _ ≤ (upperTailValuation c n p : ℝ) / secondOrderScale n :=
        div_le_div_of_nonneg_right hbounds.1 hscale.le
  · calc
      (upperTailValuation c n p : ℝ) / secondOrderScale n ≤
          ((upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) +
              ((Nat.log2 (3 * n) : ℝ) + 1)) /
            secondOrderScale n :=
        div_le_div_of_nonneg_right hbounds.2 hscale.le
      _ = (upperTailLength c n : ℝ) / secondOrderScale n /
            ((p - 1 : ℕ) : ℝ) +
          ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n := by
            field_simp [hscale.ne', hpredPos.ne']

/-- The common binary-logarithmic error in the squeeze is negligible. -/
theorem upperTailLogError_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n)
      atTop (nhds 0) := by
  have hone :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / secondOrderScale n)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop secondOrderScale_tendsto_atTop
  simpa only [add_div, add_zero] using
    log2_three_mul_normalized_tendsto_zero.add hone

/-- Paper (4.12): at every fixed prime, the actual factorial-tail valuation
has main term `c/(p-1)` on the scale `n/log n`. -/
theorem upperTailValuation_normalized_tendsto
    {c : ℝ} (hc : 0 < c) {p : ℕ} (hp : p.Prime) :
    Tendsto
      (fun n : ℕ ↦
        (upperTailValuation c n p : ℝ) / secondOrderScale n)
      atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) := by
  have hmain :
      Tendsto
        (fun n : ℕ ↦
          (upperTailLength c n : ℝ) / secondOrderScale n /
            ((p - 1 : ℕ) : ℝ))
        atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) :=
    (upperTailLength_normalized_tendsto hc).div_const
      ((p - 1 : ℕ) : ℝ)
  have hlower :
      Tendsto
        (fun n : ℕ ↦
          (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) -
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n)
        atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) := by
    simpa only [sub_zero] using
      hmain.sub upperTailLogError_normalized_tendsto_zero
  have hupper :
      Tendsto
        (fun n : ℕ ↦
          (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) +
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n)
        atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) := by
    simpa only [add_zero] using
      hmain.add upperTailLogError_normalized_tendsto_zero
  have hbounds :
      ∀ᶠ n : ℕ in atTop,
        (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) -
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n ≤
          (upperTailValuation c n p : ℝ) / secondOrderScale n ∧
        (upperTailValuation c n p : ℝ) / secondOrderScale n ≤
          (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) +
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n := by
    filter_upwards [eventually_upperTailLength_le hc,
      eventually_secondOrderScale_pos] with n htail hscale
    exact upperTailValuation_normalized_bounds hp htail hscale
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower hupper (hbounds.mono fun _ h ↦ h.1)
      (hbounds.mono fun _ h ↦ h.2)

/-- A finite set of fixed primes receives its prescribed strict lower reserve
simultaneously. -/
theorem eventually_upperTailValuation_normalized_ge_on_finset
    {c : ℝ} (hc : 0 < c) (primes : Finset ℕ) (reserve : ℕ → ℝ)
    (hprime : ∀ p ∈ primes, p.Prime)
    (hreserve : ∀ p ∈ primes,
      reserve p < c / ((p - 1 : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primes,
      reserve p ≤
        (upperTailValuation c n p : ℝ) / secondOrderScale n := by
  rw [Finset.eventually_all]
  intro p hpMem
  exact (upperTailValuation_normalized_tendsto hc (hprime p hpMem)).eventually
    (eventually_ge_nhds (hreserve p hpMem))

/-- Equivalent finite-prime reserve after multiplying by the positive scale. -/
theorem eventually_upperTailValuation_ge_mul_scale_on_finset
    {c : ℝ} (hc : 0 < c) (primes : Finset ℕ) (reserve : ℕ → ℝ)
    (hprime : ∀ p ∈ primes, p.Prime)
    (hreserve : ∀ p ∈ primes,
      reserve p < c / ((p - 1 : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primes,
      reserve p * secondOrderScale n ≤
        (upperTailValuation c n p : ℝ) := by
  have hratio := eventually_upperTailValuation_normalized_ge_on_finset
    hc primes reserve hprime hreserve
  filter_upwards [hratio, eventually_secondOrderScale_pos] with n hn hscale
  intro p hpMem
  exact (le_div_iff₀ hscale).mp (hn p hpMem)





end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.UpperProductAssembly -/
section


/-!
# Exact upper-bound product assembly

This is the division-free algebra at the end of the paper.  A central anchor
set removes the central binomial coefficient together with a divisor `D` of
the tail.  A disjoint residual tail set removes the complementary tail
product.  Their union is therefore an exact complement representation, and
the complement lemma recovers a factorization of `n!`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



theorem centralTailProduct_mul_centralFactorial (n h : ℕ) :
    centralTailProduct n h * (2 * n).factorial =
      (2 * n + h).factorial := by
  exact factorInterval_prod_mul_factorial (by omega)













end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorTailDivisibility -/
section


/-!
# From central-anchor valuation reserve to literal tail divisibility

The analytic part of the central-anchor argument produces inequalities at a
fixed finite set of primes.  This file supplies the exact arithmetic bridge:
the factorial-tail valuation is the valuation of the literal tail product,
and bounds on the finite support of the anchor divisor imply actual natural-
number divisibility.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- The literal tail product is positive, including when the tail is empty. -/
theorem centralTailProduct_pos (n h : ℕ) : 0 < centralTailProduct n h := by
  exact Finset.prod_pos fun a ha ↦ by
    have haMem : a ∈ Finset.Ioc (2 * n) (2 * n + h) := ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp haMem).1

/-- Exact valuation of the literal product over `(2n,2n+h]`. -/
theorem centralTailProduct_factorization (n h p : ℕ) :
    (centralTailProduct n h).factorization p =
      (2 * n + h).factorial.factorization p -
        (2 * n).factorial.factorization p := by
  have hproduct := congrArg (fun m : ℕ ↦ m.factorization p)
    (centralTailProduct_mul_centralFactorial n h)
  have htailNe : centralTailProduct n h ≠ 0 :=
    (centralTailProduct_pos n h).ne'
  have hfactorialNe : (2 * n).factorial ≠ 0 := Nat.factorial_ne_zero _
  change
    (centralTailProduct n h * (2 * n).factorial).factorization p =
      (2 * n + h).factorial.factorization p at hproduct
  rw [Nat.factorization_mul htailNe hfactorialNe] at hproduct
  simp only [Finsupp.add_apply] at hproduct
  omega

/-- The asymptotic module's tail valuation is literally the valuation of the
corresponding finite product. -/
theorem upperTailValuation_eq_centralTailProduct_factorization
    (c : ℝ) (n p : ℕ) :
    upperTailValuation c n p =
      (centralTailProduct n (upperTailLength c n)).factorization p := by
  rw [centralTailProduct_factorization]
  rfl





/-- It suffices to compare valuations on the displayed support bound. -/
theorem centralAnchorDivisor_dvd_centralTailProduct_of_support_bounds
    {n X B h : ℕ} {q : ℕ → ℕ}
    (hqChoice : IsLargeCentralCofactorChoice n X q)
    (hqBound : ∀ p ∈ largeCentralPrimes n X, q p ≤ B)
    (hvaluation : ∀ ℓ ∈ primesUpTo (max 2 B),
      (centralAnchorDivisor n X q).factorization ℓ ≤
        (centralTailProduct n h).factorization ℓ) :
    centralAnchorDivisor n X q ∣ centralTailProduct n h := by
  rw [← Nat.factorization_le_iff_dvd
    (centralAnchorDivisor_pos hqChoice).ne'
    (centralTailProduct_pos n h).ne']
  intro ℓ
  by_cases hℓPrime : ℓ.Prime
  · by_cases hℓDiv : ℓ ∣ centralAnchorDivisor n X q
    · apply hvaluation ℓ
      rw [mem_primesUpTo]
      exact ⟨hℓPrime,
        prime_dvd_centralAnchorDivisor_le hqChoice hqBound hℓPrime hℓDiv⟩
    · rw [Nat.factorization_eq_zero_of_not_dvd hℓDiv]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hℓPrime]
    exact Nat.zero_le _

/-- Specialized form in which the right-hand valuations are supplied by the
upper tail of length `ceil (c n / log n)`. -/
theorem centralAnchorDivisor_dvd_upperTail_of_support_bounds
    {c : ℝ} {n X B : ℕ} {q : ℕ → ℕ}
    (hqChoice : IsLargeCentralCofactorChoice n X q)
    (hqBound : ∀ p ∈ largeCentralPrimes n X, q p ≤ B)
    (hvaluation : ∀ ℓ ∈ primesUpTo (max 2 B),
      (centralAnchorDivisor n X q).factorization ℓ ≤
        upperTailValuation c n ℓ) :
    centralAnchorDivisor n X q ∣
      centralTailProduct n (upperTailLength c n) := by
  apply centralAnchorDivisor_dvd_centralTailProduct_of_support_bounds
    hqChoice hqBound
  intro ℓ hℓ
  rw [← upperTailValuation_eq_centralTailProduct_factorization]
  exact hvaluation ℓ hℓ



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorReserveAlgebra -/
section


/-!
# Finite slack algebra for the central-anchor tail reserve

This file isolates the exact comparison used after the prefix-allocation,
promotion-cost, and factorial-tail estimates have been proved.  The divisor
is the actual `centralAnchorDivisor`; its cofactor valuation is compared at a
fixed prime, and the additional promotion cost is inserted only at `2`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- With one-sixth asymptotic error on the cofactor and tail estimates and a
one-quarter promotion budget, the actual anchor-divisor valuation fits in
the actual upper tail. -/
theorem centralAnchorDivisor_factorization_le_upperTailValuation_of_slack
    {c epsilon scale : ℝ} {n X ℓ : ℕ} {q : ℕ → ℕ}
    (hc : c = C0 + epsilon) (hepsilon : 0 < epsilon)
    (hscale : 0 ≤ scale) (hℓPrime : ℓ.Prime)
    (hq : IsLargeCentralCofactorChoice n X q)
    (hcofactor :
      ((∑ p ∈ largeCentralPrimes n X,
          (q p).factorization ℓ : ℕ) : ℝ) ≤
        (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale)
    (hpromotion :
      (residualPromotionCost n X : ℝ) ≤ epsilon / 4 * scale)
    (htail :
      (c / ((ℓ - 1 : ℕ) : ℝ) -
          epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale ≤
        (upperTailValuation c n ℓ : ℝ)) :
    (centralAnchorDivisor n X q).factorization ℓ ≤
      upperTailValuation c n ℓ := by
  rw [centralAnchorDivisor_factorization hq]
  by_cases hℓTwo : ℓ = 2
  · subst ℓ
    have hcofactor' :
        ((∑ p ∈ largeCentralPrimes n X,
            (q p).factorization 2 : ℕ) : ℝ) ≤
          (C0 + epsilon / 6) * scale := by
      simpa using hcofactor
    have htail' :
        (c - epsilon / 6) * scale ≤
          (upperTailValuation c n 2 : ℝ) := by
      simpa using htail
    have hcoefficient :
        C0 + epsilon / 6 + epsilon / 4 ≤ c - epsilon / 6 := by
      rw [hc]
      linarith
    have hreal :
        ((residualPromotionCost n X +
            ∑ p ∈ largeCentralPrimes n X,
              (q p).factorization 2 : ℕ) : ℝ) ≤
          (upperTailValuation c n 2 : ℝ) := by
      rw [Nat.cast_add]
      calc
        (residualPromotionCost n X : ℝ) +
              ((∑ p ∈ largeCentralPrimes n X,
                (q p).factorization 2 : ℕ) : ℝ) ≤
            epsilon / 4 * scale + (C0 + epsilon / 6) * scale :=
          add_le_add hpromotion hcofactor'
        _ = (C0 + epsilon / 6 + epsilon / 4) * scale := by ring
        _ ≤ (c - epsilon / 6) * scale :=
          mul_le_mul_of_nonneg_right hcoefficient hscale
        _ ≤ (upperTailValuation c n 2 : ℝ) := htail'
    exact_mod_cast hreal
  · have hpredPosNat : 0 < ℓ - 1 := Nat.sub_pos_of_lt hℓPrime.one_lt
    have hpredPos : 0 < ((ℓ - 1 : ℕ) : ℝ) := by
      exact_mod_cast hpredPosNat
    have hcoefficient :
        C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ)) ≤
          c / ((ℓ - 1 : ℕ) : ℝ) -
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ)) := by
      rw [hc]
      field_simp [hpredPos.ne']
      nlinarith
    have hreal :
        ((∑ p ∈ largeCentralPrimes n X,
            (q p).factorization ℓ : ℕ) : ℝ) ≤
          (upperTailValuation c n ℓ : ℝ) :=
      hcofactor.trans <|
        (mul_le_mul_of_nonneg_right hcoefficient hscale).trans htail
    simp only [if_neg hℓTwo, zero_add]
    exact_mod_cast hreal

/-- The same slack calculation with the quantitative reserve retained.
The conclusion is written additively, so it remains meaningful before
turning the valuation comparison into natural-number divisibility. -/
theorem centralAnchorDivisor_factorization_add_reserve_le_upperTailValuation_of_slack
    {c epsilon scale : ℝ} {n X ℓ : ℕ} {q : ℕ → ℕ}
    (hc : c = C0 + epsilon) (hepsilon : 0 < epsilon)
    (hscale : 0 ≤ scale) (hℓPrime : ℓ.Prime)
    (hq : IsLargeCentralCofactorChoice n X q)
    (hcofactor :
      ((∑ p ∈ largeCentralPrimes n X,
          (q p).factorization ℓ : ℕ) : ℝ) ≤
        (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale)
    (hpromotion :
      (residualPromotionCost n X : ℝ) ≤ epsilon / 4 * scale)
    (htail :
      (c / ((ℓ - 1 : ℕ) : ℝ) -
          epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale ≤
        (upperTailValuation c n ℓ : ℝ)) :
    epsilon / (3 * ((ℓ - 1 : ℕ) : ℝ)) * scale +
        ((centralAnchorDivisor n X q).factorization ℓ : ℝ) ≤
      (upperTailValuation c n ℓ : ℝ) := by
  rw [centralAnchorDivisor_factorization hq]
  by_cases hℓTwo : ℓ = 2
  · subst ℓ
    have hcofactor' :
        ((∑ p ∈ largeCentralPrimes n X,
            (q p).factorization 2 : ℕ) : ℝ) ≤
          (C0 + epsilon / 6) * scale := by
      simpa using hcofactor
    have htail' :
        (c - epsilon / 6) * scale ≤
          (upperTailValuation c n 2 : ℝ) := by
      simpa using htail
    have hcoefficient :
        epsilon / 3 + epsilon / 4 + (C0 + epsilon / 6) ≤
          c - epsilon / 6 := by
      rw [hc]
      linarith
    calc
      epsilon / (3 * (((2 - 1 : ℕ) : ℝ))) * scale +
          (((if (2 : ℕ) = 2 then residualPromotionCost n X else 0) +
            ∑ p ∈ largeCentralPrimes n X,
              (q p).factorization 2 : ℕ) : ℝ) =
        epsilon / 3 * scale +
          (residualPromotionCost n X : ℝ) +
            ((∑ p ∈ largeCentralPrimes n X,
              (q p).factorization 2 : ℕ) : ℝ) := by
          norm_num
          ring
      _ ≤ epsilon / 3 * scale + epsilon / 4 * scale +
          (C0 + epsilon / 6) * scale := by
        gcongr
      _ = (epsilon / 3 + epsilon / 4 +
          (C0 + epsilon / 6)) * scale := by ring
      _ ≤ (c - epsilon / 6) * scale :=
        mul_le_mul_of_nonneg_right hcoefficient hscale
      _ ≤ (upperTailValuation c n 2 : ℝ) := htail'
  · have hpredPosNat : 0 < ℓ - 1 := Nat.sub_pos_of_lt hℓPrime.one_lt
    have hpredPos : 0 < ((ℓ - 1 : ℕ) : ℝ) := by
      exact_mod_cast hpredPosNat
    have hcoefficient :
        epsilon / (3 * ((ℓ - 1 : ℕ) : ℝ)) +
            (C0 / ((ℓ - 1 : ℕ) : ℝ) +
              epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) ≤
          c / ((ℓ - 1 : ℕ) : ℝ) -
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ)) := by
      rw [hc]
      field_simp [hpredPos.ne']
      linarith
    have hcofactorActual :
        (((if ℓ = 2 then residualPromotionCost n X else 0) +
          ∑ p ∈ largeCentralPrimes n X,
            (q p).factorization ℓ : ℕ) : ℝ) ≤
          (C0 / ((ℓ - 1 : ℕ) : ℝ) +
              epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale := by
      simpa only [if_neg hℓTwo, zero_add] using hcofactor
    calc
      epsilon / (3 * ((ℓ - 1 : ℕ) : ℝ)) * scale +
          (((if ℓ = 2 then residualPromotionCost n X else 0) +
            ∑ p ∈ largeCentralPrimes n X,
              (q p).factorization ℓ : ℕ) : ℝ) ≤
        epsilon / (3 * ((ℓ - 1 : ℕ) : ℝ)) * scale +
          (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale :=
        add_le_add le_rfl hcofactorActual
      _ = (epsilon / (3 * ((ℓ - 1 : ℕ) : ℝ)) +
          (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ)))) * scale := by ring
      _ ≤ (c / ((ℓ - 1 : ℕ) : ℝ) -
          epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale :=
        mul_le_mul_of_nonneg_right hcoefficient hscale
      _ ≤ (upperTailValuation c n ℓ : ℝ) := htail

/-- Simultaneous finite-support form, ending in literal natural-number
divisibility of the central-anchor divisor into the upper tail product. -/
theorem centralAnchorDivisor_dvd_upperTail_of_slack
    {c epsilon scale : ℝ} {n X B : ℕ} {q : ℕ → ℕ}
    (hc : c = C0 + epsilon) (hepsilon : 0 < epsilon)
    (hscale : 0 ≤ scale)
    (hqChoice : IsLargeCentralCofactorChoice n X q)
    (hqBound : ∀ p ∈ largeCentralPrimes n X, q p ≤ B)
    (hcofactor : ∀ ℓ ∈ primesUpTo (max 2 B),
      ((∑ p ∈ largeCentralPrimes n X,
          (q p).factorization ℓ : ℕ) : ℝ) ≤
        (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale)
    (hpromotion :
      (residualPromotionCost n X : ℝ) ≤ epsilon / 4 * scale)
    (htail : ∀ ℓ ∈ primesUpTo (max 2 B),
      (c / ((ℓ - 1 : ℕ) : ℝ) -
          epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale ≤
        (upperTailValuation c n ℓ : ℝ)) :
    centralAnchorDivisor n X q ∣
      centralTailProduct n (upperTailLength c n) := by
  apply centralAnchorDivisor_dvd_upperTail_of_support_bounds
    hqChoice hqBound
  intro ℓ hℓ
  exact centralAnchorDivisor_factorization_le_upperTailValuation_of_slack
    hc hepsilon hscale (mem_primesUpTo.mp hℓ).1 hqChoice
      (hcofactor ℓ hℓ) hpromotion (htail ℓ hℓ)

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralPromotionCostAsymptotic -/
section


/-!
# The residual central-promotion cost

This file proves the quantitative form of (4.10)--(4.11).  The elementary
promotion estimate is summed over the actual residual prime support.  A
Chebyshev estimate then shows that, after choosing one fixed cutoff
parameter, its total cost is an arbitrarily small multiple of `n / log n`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

















private theorem one_add_log_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun q : ℕ ↦ (1 + Real.log (q : ℝ)) / (q : ℝ))
      atTop (nhds 0) := by
  have hone :
      Tendsto (fun q : ℕ ↦ (1 : ℝ) / (q : ℝ)) atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  simpa only [add_div, add_zero] using
    hone.add log_natCast_div_natCast_tendsto_zero

/-- Real-budget terminal from (4.10)--(4.11).  For every positive tolerance,
one fixed `R ≥ 201` makes the actual residual promotion cost fit inside
that exact multiple of `n / log n`. -/
theorem residualPromotionCost_eventually_cast_le_mul
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : ℕ, 201 ≤ R ∧
      ∀ᶠ n : ℕ in atTop,
        (residualPromotionCost n (n / (R + 1)) : ℝ) ≤
          epsilon * secondOrderScale n := by
  obtain ⟨K, hK, hbound⟩ :=
    residualPromotionCost_fixedCutoff_uniform_bound
  have hcoefficient :
      Tendsto
        (fun q : ℕ ↦
          K * (1 + Real.log (q : ℝ)) / (q : ℝ))
        atTop (nhds 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      (tendsto_const_nhds.mul
        one_add_log_natCast_div_natCast_tendsto_zero :
          Tendsto
            (fun q : ℕ ↦
              K * ((1 + Real.log (q : ℝ)) / (q : ℝ)))
            atTop (nhds (K * 0)))
  have hsmall :
      ∀ᶠ q : ℕ in atTop,
        K * (1 + Real.log (q : ℝ)) / (q : ℝ) < epsilon :=
    hcoefficient.eventually (Iio_mem_nhds hepsilon)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  let q : ℕ := max N 202
  have hqLarge : 202 ≤ q := le_max_right N 202
  have hqSmall :
      K * (1 + Real.log (q : ℝ)) / (q : ℝ) < epsilon :=
    hN q (le_max_left N 202)
  have hfixed := hbound q (by omega)
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        (residualPromotionCost n (n / q) : ℝ) ≤
          epsilon * secondOrderScale n := by
    filter_upwards [hfixed, eventually_gt_atTop 1] with n hcost hn
    have hscale : 0 < secondOrderScale n := by
      rw [secondOrderScale]
      exact div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
    exact hcost.trans
      (mul_le_mul_of_nonneg_right hqSmall.le hscale.le)
  refine ⟨q - 1, by omega, ?_⟩
  have hqEq : q - 1 + 1 = q := by omega
  simpa only [hqEq] using hevent



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorCutoff -/
section


/-!
# The fixed-prefix central-anchor cutoff

For a fixed prefix depth `R`, the paper splits the central prime blocks at
`n / (R + 1)`.  This file gives an explicit sufficient threshold for all
scale separations and then connects that literal cutoff directly to the
large-prime routing and central-anchor product APIs.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section





theorem centralAnchorCutoffThreshold_pos (R : ℕ) :
    0 < centralAnchorCutoffThreshold R := by
  simp [centralAnchorCutoffThreshold]

/-- At the explicit threshold, the cutoff is at least `4(R+1)`. -/
theorem four_mul_succ_le_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    4 * (R + 1) ≤ centralAnchorCutoff R n := by
  rw [centralAnchorCutoff, Nat.le_div_iff_mul_le (by omega)]
  simpa only [centralAnchorCutoffThreshold, pow_two, mul_assoc] using hn

/-- The cutoff lies strictly above every cofactor in rows `1,…,R`. -/
theorem two_mul_add_one_lt_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * R + 1 < centralAnchorCutoff R n := by
  have hfour := four_mul_succ_le_centralAnchorCutoff hn
  omega

/-- The explicit threshold also puts `2n` strictly below the cutoff square. -/
theorem two_mul_lt_centralAnchorCutoff_sq
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 * n < (centralAnchorCutoff R n) ^ 2 := by
  let X := centralAnchorCutoff R n
  have hX : 4 * (R + 1) ≤ X := by
    simpa only [X] using four_mul_succ_le_centralAnchorCutoff hn
  have hXPos : 0 < X := by omega
  have hnUpper : n < (R + 1) * (X + 1) := by
    simpa only [X, centralAnchorCutoff] using
      Nat.lt_mul_div_succ n (by omega : 0 < R + 1)
  have hlinear : 2 * (R + 1) * (X + 1) ≤ X ^ 2 := by
    calc
      2 * (R + 1) * (X + 1) ≤ 2 * (R + 1) * (2 * X) := by
        exact Nat.mul_le_mul_left (2 * (R + 1)) (by omega)
      _ = (4 * (R + 1)) * X := by ring
      _ ≤ X * X := Nat.mul_le_mul_right X hX
      _ = X ^ 2 := by ring
  calc
    2 * n < 2 * ((R + 1) * (X + 1)) :=
      (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hnUpper
    _ = 2 * (R + 1) * (X + 1) := by ring
    _ ≤ X ^ 2 := hlinear



theorem two_le_centralAnchorCutoff
    {R n : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n) :
    2 ≤ centralAnchorCutoff R n := by
  have hsep := two_mul_add_one_lt_centralAnchorCutoff hn
  omega







/-- A prime above `n/(R+1)` has quotient row at most `R`. -/
theorem div_le_fixedPrefix_of_centralAnchorCutoff_lt
    {R n p : ℕ} (hp : centralAnchorCutoff R n < p) :
    n / p ≤ R := by
  have hpPos : 0 < p := by omega
  have hdiv : n / (R + 1) < p := by
    simpa only [centralAnchorCutoff] using hp
  have hnUpper : n < p * (R + 1) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < R + 1)).1 hdiv
  have hrow : n / p < R + 1 :=
    (Nat.div_lt_iff_lt_mul hpPos).2 (by
      simpa only [Nat.mul_comm] using hnUpper)
  omega

theorem largeCentralPrime_div_le_fixedPrefix
    {R n p : ℕ}
    (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    n / p ≤ R :=
  div_le_fixedPrefix_of_centralAnchorCutoff_lt
    (largeCentralPrimes_gt hp)

/-- Routing at the literal cutoff lands in row zero or a positive row no
larger than the fixed prefix depth. -/
theorem largeCentralPrime_rowZero_or_fixedPrefix
    {R n p : ℕ} (hn : centralAnchorCutoffThreshold R ≤ n)
    (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      ((n < p ∧ p ≤ 2 * n) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r) := by
  have hnPos : 0 < n :=
    (centralAnchorCutoffThreshold_pos R).trans_le hn
  have hroute := largeCentralPrime_rowZero_or_stationary hnPos
    (two_mul_lt_centralAnchorCutoff_sq hn) hp
  refine ⟨hroute.1, ?_⟩
  rcases hroute.2 with hzero | ⟨r, hrPos, hr, hpRow⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨r, hrPos, by
      rw [hr]
      exact largeCentralPrime_div_le_fixedPrefix hp, hr, hpRow⟩

/-- Every routed cofactor above the literal cutoff is in the fixed
cofactor prefix `[1,2R+1]`. -/
theorem largeCentralCofactor_le_fixedPrefix
    {R n : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n (centralAnchorCutoff R n)) :
    q p ≤ 2 * R + 1 := by
  rcases hq p hp with hzero |
      ⟨r, _hrPos, hr, _hpRow, _hqLower, hqUpper⟩
  · omega
  · have hrUpper : r ≤ R := by
      rw [hr]
      exact largeCentralPrime_div_le_fixedPrefix hp
    omega

















/-- Direct exact-product corollary at the fixed-`R` cutoff. -/
theorem fullCentralAnchors_prod_centralAnchorCutoff
    {R n : ℕ} {q : ℕ → ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    (hq : IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q) :
    (fullCentralAnchors n (centralAnchorCutoff R n) q).prod id =
      Nat.choose (2 * n) n *
        centralAnchorDivisor n (centralAnchorCutoff R n) q := by
  exact fullCentralAnchors_prod
    ((centralAnchorCutoffThreshold_pos R).trans_le hn)
    (two_le_centralAnchorCutoff hn)
    (two_mul_lt_centralAnchorCutoff_sq hn) hq



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateStructuralChecks -/
section


/-!
# Bounded structural checks for the finite allocation certificate

Every decision here sees at most one twenty-row block, except for the three
linear whole-array audits (length, validity, and primality).
-/

namespace Erdos390.WholePaper

open AllocationEntry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0









theorem allocationPrimeBlockPerm {b : ℕ} (hb : b ≤ 9) :
    (finiteAllocationRowBlockEntries b).Perm
      ((finiteAllocationPrimeBlockBuckets b).flatMap fun bucket => bucket.2) := by
  interval_cases b <;> decide



theorem allocationPrimeLabels {b : ℕ} (hb : b ≤ 9) :
    allocationKeyLabeled (fun e => e.cofactor)
      (finiteAllocationPrimeBlockBuckets b) := by
  unfold allocationKeyLabeled
  interval_cases b <;> decide











private theorem allocationCofactorPrimeCheck_eq_true :
    allocationCofactorPrimeCheck = true := by
  decide

theorem finiteAllocationEntries_cofactor_prime {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntries) : e.cofactor.Prime := by
  exact of_decide_eq_true
    ((List.all_eq_true.mp allocationCofactorPrimeCheck_eq_true) e he)

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateCapacityChecks1 -/
section


/-! Bounded kernel checks for the finite allocation certificate (capacity batch 1). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawCapacityCrossLE_2 :
    (rawPrimeLoad 2).CrossLE (rawCapacity 2) := by decide
@[simp] theorem rawCapacityCrossLE_3 :
    (rawPrimeLoad 3).CrossLE (rawCapacity 3) := by decide
@[simp] theorem rawCapacityCrossLE_5 :
    (rawPrimeLoad 5).CrossLE (rawCapacity 5) := by decide
@[simp] theorem rawCapacityCrossLE_7 :
    (rawPrimeLoad 7).CrossLE (rawCapacity 7) := by decide
@[simp] theorem rawCapacityCrossLE_11 :
    (rawPrimeLoad 11).CrossLE (rawCapacity 11) := by decide
@[simp] theorem rawCapacityCrossLE_13 :
    (rawPrimeLoad 13).CrossLE (rawCapacity 13) := by decide
@[simp] theorem rawCapacityCrossLE_17 :
    (rawPrimeLoad 17).CrossLE (rawCapacity 17) := by decide
@[simp] theorem rawCapacityCrossLE_19 :
    (rawPrimeLoad 19).CrossLE (rawCapacity 19) := by decide
@[simp] theorem rawCapacityCrossLE_23 :
    (rawPrimeLoad 23).CrossLE (rawCapacity 23) := by decide
@[simp] theorem rawCapacityCrossLE_29 :
    (rawPrimeLoad 29).CrossLE (rawCapacity 29) := by decide
@[simp] theorem rawCapacityCrossLE_31 :
    (rawPrimeLoad 31).CrossLE (rawCapacity 31) := by decide
@[simp] theorem rawCapacityCrossLE_37 :
    (rawPrimeLoad 37).CrossLE (rawCapacity 37) := by decide
@[simp] theorem rawCapacityCrossLE_41 :
    (rawPrimeLoad 41).CrossLE (rawCapacity 41) := by decide
@[simp] theorem rawCapacityCrossLE_43 :
    (rawPrimeLoad 43).CrossLE (rawCapacity 43) := by decide
@[simp] theorem rawCapacityCrossLE_47 :
    (rawPrimeLoad 47).CrossLE (rawCapacity 47) := by decide
@[simp] theorem rawCapacityCrossLE_53 :
    (rawPrimeLoad 53).CrossLE (rawCapacity 53) := by decide
@[simp] theorem rawCapacityCrossLE_59 :
    (rawPrimeLoad 59).CrossLE (rawCapacity 59) := by decide
@[simp] theorem rawCapacityCrossLE_61 :
    (rawPrimeLoad 61).CrossLE (rawCapacity 61) := by decide
@[simp] theorem rawCapacityCrossLE_67 :
    (rawPrimeLoad 67).CrossLE (rawCapacity 67) := by decide
@[simp] theorem rawCapacityCrossLE_71 :
    (rawPrimeLoad 71).CrossLE (rawCapacity 71) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateCapacityChecks2 -/
section


/-! Bounded kernel checks for the finite allocation certificate (capacity batch 2). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawCapacityCrossLE_73 :
    (rawPrimeLoad 73).CrossLE (rawCapacity 73) := by decide
@[simp] theorem rawCapacityCrossLE_79 :
    (rawPrimeLoad 79).CrossLE (rawCapacity 79) := by decide
@[simp] theorem rawCapacityCrossLE_83 :
    (rawPrimeLoad 83).CrossLE (rawCapacity 83) := by decide
@[simp] theorem rawCapacityCrossLE_89 :
    (rawPrimeLoad 89).CrossLE (rawCapacity 89) := by decide
@[simp] theorem rawCapacityCrossLE_97 :
    (rawPrimeLoad 97).CrossLE (rawCapacity 97) := by decide
@[simp] theorem rawCapacityCrossLE_101 :
    (rawPrimeLoad 101).CrossLE (rawCapacity 101) := by decide
@[simp] theorem rawCapacityCrossLE_103 :
    (rawPrimeLoad 103).CrossLE (rawCapacity 103) := by decide
@[simp] theorem rawCapacityCrossLE_107 :
    (rawPrimeLoad 107).CrossLE (rawCapacity 107) := by decide
@[simp] theorem rawCapacityCrossLE_109 :
    (rawPrimeLoad 109).CrossLE (rawCapacity 109) := by decide
@[simp] theorem rawCapacityCrossLE_113 :
    (rawPrimeLoad 113).CrossLE (rawCapacity 113) := by decide
@[simp] theorem rawCapacityCrossLE_127 :
    (rawPrimeLoad 127).CrossLE (rawCapacity 127) := by decide
@[simp] theorem rawCapacityCrossLE_131 :
    (rawPrimeLoad 131).CrossLE (rawCapacity 131) := by decide
@[simp] theorem rawCapacityCrossLE_137 :
    (rawPrimeLoad 137).CrossLE (rawCapacity 137) := by decide
@[simp] theorem rawCapacityCrossLE_139 :
    (rawPrimeLoad 139).CrossLE (rawCapacity 139) := by decide
@[simp] theorem rawCapacityCrossLE_149 :
    (rawPrimeLoad 149).CrossLE (rawCapacity 149) := by decide
@[simp] theorem rawCapacityCrossLE_151 :
    (rawPrimeLoad 151).CrossLE (rawCapacity 151) := by decide
@[simp] theorem rawCapacityCrossLE_157 :
    (rawPrimeLoad 157).CrossLE (rawCapacity 157) := by decide
@[simp] theorem rawCapacityCrossLE_163 :
    (rawPrimeLoad 163).CrossLE (rawCapacity 163) := by decide
@[simp] theorem rawCapacityCrossLE_167 :
    (rawPrimeLoad 167).CrossLE (rawCapacity 167) := by decide
@[simp] theorem rawCapacityCrossLE_173 :
    (rawPrimeLoad 173).CrossLE (rawCapacity 173) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateCapacityChecks3 -/
section


/-! Bounded kernel checks for the finite allocation certificate (capacity batch 3). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawCapacityCrossLE_179 :
    (rawPrimeLoad 179).CrossLE (rawCapacity 179) := by decide
@[simp] theorem rawCapacityCrossLE_181 :
    (rawPrimeLoad 181).CrossLE (rawCapacity 181) := by decide
@[simp] theorem rawCapacityCrossLE_191 :
    (rawPrimeLoad 191).CrossLE (rawCapacity 191) := by decide
@[simp] theorem rawCapacityCrossLE_193 :
    (rawPrimeLoad 193).CrossLE (rawCapacity 193) := by decide
@[simp] theorem rawCapacityCrossLE_197 :
    (rawPrimeLoad 197).CrossLE (rawCapacity 197) := by decide
@[simp] theorem rawCapacityCrossLE_199 :
    (rawPrimeLoad 199).CrossLE (rawCapacity 199) := by decide
@[simp] theorem rawCapacityCrossLE_211 :
    (rawPrimeLoad 211).CrossLE (rawCapacity 211) := by decide
@[simp] theorem rawCapacityCrossLE_223 :
    (rawPrimeLoad 223).CrossLE (rawCapacity 223) := by decide
@[simp] theorem rawCapacityCrossLE_227 :
    (rawPrimeLoad 227).CrossLE (rawCapacity 227) := by decide
@[simp] theorem rawCapacityCrossLE_229 :
    (rawPrimeLoad 229).CrossLE (rawCapacity 229) := by decide
@[simp] theorem rawCapacityCrossLE_233 :
    (rawPrimeLoad 233).CrossLE (rawCapacity 233) := by decide
@[simp] theorem rawCapacityCrossLE_239 :
    (rawPrimeLoad 239).CrossLE (rawCapacity 239) := by decide
@[simp] theorem rawCapacityCrossLE_241 :
    (rawPrimeLoad 241).CrossLE (rawCapacity 241) := by decide
@[simp] theorem rawCapacityCrossLE_251 :
    (rawPrimeLoad 251).CrossLE (rawCapacity 251) := by decide
@[simp] theorem rawCapacityCrossLE_257 :
    (rawPrimeLoad 257).CrossLE (rawCapacity 257) := by decide
@[simp] theorem rawCapacityCrossLE_263 :
    (rawPrimeLoad 263).CrossLE (rawCapacity 263) := by decide
@[simp] theorem rawCapacityCrossLE_269 :
    (rawPrimeLoad 269).CrossLE (rawCapacity 269) := by decide
@[simp] theorem rawCapacityCrossLE_271 :
    (rawPrimeLoad 271).CrossLE (rawCapacity 271) := by decide
@[simp] theorem rawCapacityCrossLE_277 :
    (rawPrimeLoad 277).CrossLE (rawCapacity 277) := by decide
@[simp] theorem rawCapacityCrossLE_281 :
    (rawPrimeLoad 281).CrossLE (rawCapacity 281) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateCapacityChecks4 -/
section


/-! Bounded kernel checks for the finite allocation certificate (capacity batch 4). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawCapacityCrossLE_283 :
    (rawPrimeLoad 283).CrossLE (rawCapacity 283) := by decide
@[simp] theorem rawCapacityCrossLE_293 :
    (rawPrimeLoad 293).CrossLE (rawCapacity 293) := by decide
@[simp] theorem rawCapacityCrossLE_307 :
    (rawPrimeLoad 307).CrossLE (rawCapacity 307) := by decide
@[simp] theorem rawCapacityCrossLE_311 :
    (rawPrimeLoad 311).CrossLE (rawCapacity 311) := by decide
@[simp] theorem rawCapacityCrossLE_313 :
    (rawPrimeLoad 313).CrossLE (rawCapacity 313) := by decide
@[simp] theorem rawCapacityCrossLE_317 :
    (rawPrimeLoad 317).CrossLE (rawCapacity 317) := by decide
@[simp] theorem rawCapacityCrossLE_331 :
    (rawPrimeLoad 331).CrossLE (rawCapacity 331) := by decide
@[simp] theorem rawCapacityCrossLE_337 :
    (rawPrimeLoad 337).CrossLE (rawCapacity 337) := by decide
@[simp] theorem rawCapacityCrossLE_347 :
    (rawPrimeLoad 347).CrossLE (rawCapacity 347) := by decide
@[simp] theorem rawCapacityCrossLE_349 :
    (rawPrimeLoad 349).CrossLE (rawCapacity 349) := by decide
@[simp] theorem rawCapacityCrossLE_353 :
    (rawPrimeLoad 353).CrossLE (rawCapacity 353) := by decide
@[simp] theorem rawCapacityCrossLE_359 :
    (rawPrimeLoad 359).CrossLE (rawCapacity 359) := by decide
@[simp] theorem rawCapacityCrossLE_367 :
    (rawPrimeLoad 367).CrossLE (rawCapacity 367) := by decide
@[simp] theorem rawCapacityCrossLE_373 :
    (rawPrimeLoad 373).CrossLE (rawCapacity 373) := by decide
@[simp] theorem rawCapacityCrossLE_379 :
    (rawPrimeLoad 379).CrossLE (rawCapacity 379) := by decide
@[simp] theorem rawCapacityCrossLE_383 :
    (rawPrimeLoad 383).CrossLE (rawCapacity 383) := by decide
@[simp] theorem rawCapacityCrossLE_389 :
    (rawPrimeLoad 389).CrossLE (rawCapacity 389) := by decide
@[simp] theorem rawCapacityCrossLE_397 :
    (rawPrimeLoad 397).CrossLE (rawCapacity 397) := by decide
@[simp] theorem rawCapacityCrossLE_401 :
    (rawPrimeLoad 401).CrossLE (rawCapacity 401) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateOverlapChecks1 -/
section


/-! Bounded kernel checks for the finite allocation certificate (overlap batch 1). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawOverlapCrossLE_211 :
    (RawFraction.add (rawPrimeLoad 211) (rawTailOverlap 211)).CrossLE
      (rawCapacity 211) := by decide
@[simp] theorem rawOverlapCrossLE_223 :
    (RawFraction.add (rawPrimeLoad 223) (rawTailOverlap 223)).CrossLE
      (rawCapacity 223) := by decide
@[simp] theorem rawOverlapCrossLE_227 :
    (RawFraction.add (rawPrimeLoad 227) (rawTailOverlap 227)).CrossLE
      (rawCapacity 227) := by decide
@[simp] theorem rawOverlapCrossLE_229 :
    (RawFraction.add (rawPrimeLoad 229) (rawTailOverlap 229)).CrossLE
      (rawCapacity 229) := by decide
@[simp] theorem rawOverlapCrossLE_233 :
    (RawFraction.add (rawPrimeLoad 233) (rawTailOverlap 233)).CrossLE
      (rawCapacity 233) := by decide
@[simp] theorem rawOverlapCrossLE_239 :
    (RawFraction.add (rawPrimeLoad 239) (rawTailOverlap 239)).CrossLE
      (rawCapacity 239) := by decide
@[simp] theorem rawOverlapCrossLE_241 :
    (RawFraction.add (rawPrimeLoad 241) (rawTailOverlap 241)).CrossLE
      (rawCapacity 241) := by decide
@[simp] theorem rawOverlapCrossLE_251 :
    (RawFraction.add (rawPrimeLoad 251) (rawTailOverlap 251)).CrossLE
      (rawCapacity 251) := by decide
@[simp] theorem rawOverlapCrossLE_257 :
    (RawFraction.add (rawPrimeLoad 257) (rawTailOverlap 257)).CrossLE
      (rawCapacity 257) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateOverlapChecks2 -/
section


/-! Bounded kernel checks for the finite allocation certificate (overlap batch 2). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawOverlapCrossLE_263 :
    (RawFraction.add (rawPrimeLoad 263) (rawTailOverlap 263)).CrossLE
      (rawCapacity 263) := by decide
@[simp] theorem rawOverlapCrossLE_269 :
    (RawFraction.add (rawPrimeLoad 269) (rawTailOverlap 269)).CrossLE
      (rawCapacity 269) := by decide
@[simp] theorem rawOverlapCrossLE_271 :
    (RawFraction.add (rawPrimeLoad 271) (rawTailOverlap 271)).CrossLE
      (rawCapacity 271) := by decide
@[simp] theorem rawOverlapCrossLE_277 :
    (RawFraction.add (rawPrimeLoad 277) (rawTailOverlap 277)).CrossLE
      (rawCapacity 277) := by decide
@[simp] theorem rawOverlapCrossLE_281 :
    (RawFraction.add (rawPrimeLoad 281) (rawTailOverlap 281)).CrossLE
      (rawCapacity 281) := by decide
@[simp] theorem rawOverlapCrossLE_283 :
    (RawFraction.add (rawPrimeLoad 283) (rawTailOverlap 283)).CrossLE
      (rawCapacity 283) := by decide
@[simp] theorem rawOverlapCrossLE_293 :
    (RawFraction.add (rawPrimeLoad 293) (rawTailOverlap 293)).CrossLE
      (rawCapacity 293) := by decide
@[simp] theorem rawOverlapCrossLE_307 :
    (RawFraction.add (rawPrimeLoad 307) (rawTailOverlap 307)).CrossLE
      (rawCapacity 307) := by decide
@[simp] theorem rawOverlapCrossLE_311 :
    (RawFraction.add (rawPrimeLoad 311) (rawTailOverlap 311)).CrossLE
      (rawCapacity 311) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateOverlapChecks3 -/
section


/-! Bounded kernel checks for the finite allocation certificate (overlap batch 3). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawOverlapCrossLE_313 :
    (RawFraction.add (rawPrimeLoad 313) (rawTailOverlap 313)).CrossLE
      (rawCapacity 313) := by decide
@[simp] theorem rawOverlapCrossLE_317 :
    (RawFraction.add (rawPrimeLoad 317) (rawTailOverlap 317)).CrossLE
      (rawCapacity 317) := by decide
@[simp] theorem rawOverlapCrossLE_331 :
    (RawFraction.add (rawPrimeLoad 331) (rawTailOverlap 331)).CrossLE
      (rawCapacity 331) := by decide
@[simp] theorem rawOverlapCrossLE_337 :
    (RawFraction.add (rawPrimeLoad 337) (rawTailOverlap 337)).CrossLE
      (rawCapacity 337) := by decide
@[simp] theorem rawOverlapCrossLE_347 :
    (RawFraction.add (rawPrimeLoad 347) (rawTailOverlap 347)).CrossLE
      (rawCapacity 347) := by decide
@[simp] theorem rawOverlapCrossLE_349 :
    (RawFraction.add (rawPrimeLoad 349) (rawTailOverlap 349)).CrossLE
      (rawCapacity 349) := by decide
@[simp] theorem rawOverlapCrossLE_353 :
    (RawFraction.add (rawPrimeLoad 353) (rawTailOverlap 353)).CrossLE
      (rawCapacity 353) := by decide
@[simp] theorem rawOverlapCrossLE_359 :
    (RawFraction.add (rawPrimeLoad 359) (rawTailOverlap 359)).CrossLE
      (rawCapacity 359) := by decide
@[simp] theorem rawOverlapCrossLE_367 :
    (RawFraction.add (rawPrimeLoad 367) (rawTailOverlap 367)).CrossLE
      (rawCapacity 367) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificateOverlapChecks4 -/
section


/-! Bounded kernel checks for the finite allocation certificate (overlap batch 4). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawOverlapCrossLE_373 :
    (RawFraction.add (rawPrimeLoad 373) (rawTailOverlap 373)).CrossLE
      (rawCapacity 373) := by decide
@[simp] theorem rawOverlapCrossLE_379 :
    (RawFraction.add (rawPrimeLoad 379) (rawTailOverlap 379)).CrossLE
      (rawCapacity 379) := by decide
@[simp] theorem rawOverlapCrossLE_383 :
    (RawFraction.add (rawPrimeLoad 383) (rawTailOverlap 383)).CrossLE
      (rawCapacity 383) := by decide
@[simp] theorem rawOverlapCrossLE_389 :
    (RawFraction.add (rawPrimeLoad 389) (rawTailOverlap 389)).CrossLE
      (rawCapacity 389) := by decide
@[simp] theorem rawOverlapCrossLE_397 :
    (RawFraction.add (rawPrimeLoad 397) (rawTailOverlap 397)).CrossLE
      (rawCapacity 397) := by decide
@[simp] theorem rawOverlapCrossLE_401 :
    (RawFraction.add (rawPrimeLoad 401) (rawTailOverlap 401)).CrossLE
      (rawCapacity 401) := by decide

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationCertificate -/
section


/-!
# Kernel-checked finite allocation certificate

This file internalizes the exact rational checker accompanying Section 4 of
the paper.  The finite computations use ordinary kernel reduction through
`decide`; in particular, no native-code decision procedure is used.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

open AllocationEntry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

















/-! ## Exact structural checks -/











private theorem sum_map_eq_of_perm {α : Type*} {l₁ l₂ : List α}
    (h : l₁.Perm l₂) (f : α → ℚ) :
    (l₁.map f).sum = (l₂.map f).sum := by
  exact (h.map f).foldr_eq 0









private theorem primeBlockPerm {b : ℕ} (hb : b ≤ 9) :
    (finiteAllocationRowBlockEntries b).Perm
      ((finiteAllocationPrimeBlockBuckets b).flatMap fun bucket => bucket.2) := by
  exact allocationPrimeBlockPerm hb



private theorem primeLabels {b : ℕ} (hb : b ≤ 9) :
    keyLabeled (fun e => e.cofactor) (finiteAllocationPrimeBlockBuckets b) := by
  exact allocationPrimeLabels hb



























private theorem primeBlockIndicatorSum {b p : ℕ} (hb : b ≤ 9) :
    ((finiteAllocationRowBlockEntries b).map fun e =>
        if e.cofactor = p then e.value else 0).sum =
      ((selectPrimeEntries p (finiteAllocationPrimeBlockBuckets b)).map
        fun e => e.value).sum := by
  calc
    _ = (((finiteAllocationPrimeBlockBuckets b).flatMap fun bucket => bucket.2).map
          fun e => if e.cofactor = p then e.value else 0).sum :=
      sum_map_eq_of_perm (primeBlockPerm hb) _
    _ = _ := indicator_sum_buckets (fun e => e.cofactor) p _ (primeLabels hb)



private theorem finitePrimeIndicatorListMass_eq (p : ℕ) :
    (finiteAllocationEntries.map fun e =>
        if e.cofactor = p then e.value else 0).sum =
      finitePrimeIndicatorListLoad p := by
  rw [finiteAllocationEntries, finitePrimeIndicatorListLoad,
    finiteAllocationPrimeEntries]
  simp only [List.map_append, List.sum_append]
  rw [primeBlockIndicatorSum (b := 0) (by omega),
    primeBlockIndicatorSum (b := 1) (by omega),
    primeBlockIndicatorSum (b := 2) (by omega),
    primeBlockIndicatorSum (b := 3) (by omega),
    primeBlockIndicatorSum (b := 4) (by omega),
    primeBlockIndicatorSum (b := 5) (by omega),
    primeBlockIndicatorSum (b := 6) (by omega),
    primeBlockIndicatorSum (b := 7) (by omega),
    primeBlockIndicatorSum (b := 8) (by omega),
    primeBlockIndicatorSum (b := 9) (by omega)]



theorem finitePrimeIndicatorLoad_eq_list (ℓ : ℕ) :
    finitePrimeIndicatorLoad ℓ = finitePrimeIndicatorListLoad ℓ := by
  calc
    finitePrimeIndicatorLoad ℓ =
        (finiteAllocationEntries.map fun e =>
          if e.cofactor = ℓ then e.value else 0).sum := by
      simpa [finitePrimeIndicatorLoad, finiteAllocationEntrySet] using
        (List.sum_toFinset
          (fun e : AllocationEntry => if e.cofactor = ℓ then e.value else 0)
          finiteAllocationEntries_nodup)
    _ = finitePrimeIndicatorListLoad ℓ := finitePrimeIndicatorListMass_eq ℓ











theorem RawFraction.toRat_le_of_crossLE {a b : RawFraction}
    (ha : 0 < a.denominator) (hb : 0 < b.denominator)
    (hcross : a.CrossLE b) : a.toRat ≤ b.toRat := by
  exact (div_le_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hb)).2
    (by exact_mod_cast hcross)



theorem rawPrimeLoad_denominator_pos (p : ℕ) :
    0 < (rawPrimeLoad p).denominator := by
  apply RawFraction.sum_denominator_pos
  intro e _
  simp [RawFraction.ofEntry]



theorem rawCapacity_denominator_pos {p : ℕ} (hp : 1 < p) :
    0 < (rawCapacity p).denominator := by
  simp [rawCapacity]
  omega

theorem rawTailOverlap_denominator_pos (p : ℕ) :
    0 < (rawTailOverlap p).denominator := by
  apply RawFraction.sum_denominator_pos
  intro r _
  exact rawAlpha_denominator_pos r



theorem rawPrimeLoad_toRat (p : ℕ) :
    (rawPrimeLoad p).toRat = finitePrimeIndicatorListLoad p := by
  rw [rawPrimeLoad, RawFraction.sum_toRat]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    rfl
  · intro e _
    simp [RawFraction.ofEntry]



theorem rawCapacity_toRat {p : ℕ} (hp : 1 < p) :
    (rawCapacity p).toRat = C0Rat / (((p - 1 : ℕ) : ℚ)) := by
  rw [C0Rat_eq]
  norm_num [rawCapacity, RawFraction.toRat]
  push_cast [Nat.one_le_iff_ne_zero.mpr (by omega : p ≠ 0)]
  field_simp

theorem rawTailOverlap_toRat {p : ℕ} (hp201 : 201 < p) :
    (rawTailOverlap p).toRat = finiteTailOverlap p := by
  let lo := max 201 (previousPrime p)
  let rows := List.range' lo ((p - 1) + 1 - lo)
  have hlo : lo ≤ p - 1 := by
    dsimp [lo]
    have hprev : previousPrime p ≤ p - 1 := Nat.findGreatest_le (p - 1)
    omega
  have hrows : rows.toFinset = Finset.Icc lo (p - 1) := by
    ext r
    simp only [rows, List.mem_toFinset, List.mem_range'_1, Finset.mem_Icc]
    omega
  rw [rawTailOverlap, show max 201 (previousPrime p) = lo by rfl,
    show List.range' lo ((p - 1) + 1 - lo) = rows by rfl,
    RawFraction.sum_toRat]
  · calc
      (rows.map fun r => (rawAlpha r).toRat).sum =
          (rows.map alpha).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro r _
            exact rawAlpha_toRat r
      _ = ∑ r ∈ rows.toFinset, alpha r := by
            symm
            exact List.sum_toFinset alpha List.nodup_range'
      _ = finiteTailOverlap p := by
            rw [hrows]
            rfl
  · intro r _
    exact rawAlpha_denominator_pos r





theorem finiteAllocationEntrySet_cofactor_prime {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntrySet) : e.cofactor.Prime :=
  finiteAllocationEntries_cofactor_prime
    (finiteAllocationEntrySet_mem_iff.mp he)















/-! ## Sparse sums equal the literal coordinate sums -/





/-- The literal double coordinate sum in the definition of
`lambda_ell^{fin}` equals the sparse entry sum checked below. -/
theorem finitePrimeLoad_eq_coordinate_sum (ℓ : ℕ) :
    finitePrimeLoad ℓ =
      ∑ r ∈ Finset.Icc 1 200,
        ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
          (q.factorization ℓ : ℚ) * finiteAllocation r q := by
  classical
  symm
  calc
    (∑ r ∈ Finset.Icc 1 200,
        ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
          (q.factorization ℓ : ℚ) * finiteAllocation r q) =
        ∑ r ∈ Finset.Icc 1 200,
          ∑ e ∈ finiteAllocationEntrySet,
            if e.row = r then
              (e.cofactor.factorization ℓ : ℚ) * e.value else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          exact finiteAllocation_weighted_row_sum
            (fun q => (q.factorization ℓ : ℚ)) r
    _ = ∑ e ∈ finiteAllocationEntrySet,
          (e.cofactor.factorization ℓ : ℚ) * e.value := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro e he
          have hvalid := finiteAllocationEntrySet_valid he
          have hrmem : e.row ∈ Finset.Icc 1 200 := by
            exact Finset.mem_Icc.mpr ⟨hvalid.1, hvalid.2.1⟩
          rw [Finset.sum_eq_single e.row]
          · simp
          · intro r hr hne
            simp [hne.symm]
          · exact fun hnot => (hnot hrmem).elim
    _ = finitePrimeLoad ℓ := rfl

theorem finitePrimeLoad_eq_indicator (ℓ : ℕ) :
    finitePrimeLoad ℓ = finitePrimeIndicatorLoad ℓ := by
  classical
  rw [finitePrimeLoad, finitePrimeIndicatorLoad]
  apply Finset.sum_congr rfl
  intro e he
  have hp := finiteAllocationEntrySet_cofactor_prime he
  rw [hp.factorization]
  simp [Finsupp.single_apply]

/-- No listed cofactor exceeds `401`, so larger primes have zero finite load. -/
theorem finitePrimeLoad_eq_zero_of_gt_401 {ℓ : ℕ} (hℓ401 : 401 < ℓ) :
    finitePrimeLoad ℓ = 0 := by
  classical
  rw [finitePrimeLoad_eq_indicator, finitePrimeIndicatorLoad]
  apply Finset.sum_eq_zero
  intro e he
  rw [if_neg]
  intro heq
  have hvalid := finiteAllocationEntrySet_valid he
  have hr200 : e.row ≤ 200 := hvalid.2.1
  have hqbound : e.cofactor ≤ 2 * e.row + 1 := hvalid.2.2.2.1
  have hcofactor : e.cofactor ≤ 401 := by omega
  omega

/-! ## Kernel-checked rational identities and inequalities -/









private theorem rawCapacityCrossLE {p : ℕ} (hp : p.Prime) (hp401 : p ≤ 401) :
    (rawPrimeLoad p).CrossLE (rawCapacity p) := by
  by_cases h21 : p ≤ 21
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_2, rawCapacityCrossLE_3, rawCapacityCrossLE_5, rawCapacityCrossLE_7, rawCapacityCrossLE_11, rawCapacityCrossLE_13, rawCapacityCrossLE_17, rawCapacityCrossLE_19]
  by_cases h41 : p ≤ 41
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_23, rawCapacityCrossLE_29, rawCapacityCrossLE_31, rawCapacityCrossLE_37, rawCapacityCrossLE_41]
  by_cases h61 : p ≤ 61
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_43, rawCapacityCrossLE_47, rawCapacityCrossLE_53, rawCapacityCrossLE_59, rawCapacityCrossLE_61]
  by_cases h81 : p ≤ 81
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_67, rawCapacityCrossLE_71, rawCapacityCrossLE_73, rawCapacityCrossLE_79]
  by_cases h101 : p ≤ 101
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_83, rawCapacityCrossLE_89, rawCapacityCrossLE_97, rawCapacityCrossLE_101]
  by_cases h121 : p ≤ 121
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_103, rawCapacityCrossLE_107, rawCapacityCrossLE_109, rawCapacityCrossLE_113]
  by_cases h141 : p ≤ 141
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_127, rawCapacityCrossLE_131, rawCapacityCrossLE_137, rawCapacityCrossLE_139]
  by_cases h161 : p ≤ 161
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_149, rawCapacityCrossLE_151, rawCapacityCrossLE_157]
  by_cases h181 : p ≤ 181
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_163, rawCapacityCrossLE_167, rawCapacityCrossLE_173, rawCapacityCrossLE_179, rawCapacityCrossLE_181]
  by_cases h201 : p ≤ 201
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_191, rawCapacityCrossLE_193, rawCapacityCrossLE_197, rawCapacityCrossLE_199]
  by_cases h221 : p ≤ 221
  · have hpEq : p = 211 := by
      interval_cases p <;> norm_num at hp
      rfl
    subst p
    exact rawCapacityCrossLE_211
  by_cases h241 : p ≤ 241
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_223, rawCapacityCrossLE_227, rawCapacityCrossLE_229, rawCapacityCrossLE_233, rawCapacityCrossLE_239, rawCapacityCrossLE_241]
  by_cases h261 : p ≤ 261
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_251, rawCapacityCrossLE_257]
  by_cases h281 : p ≤ 281
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_263, rawCapacityCrossLE_269, rawCapacityCrossLE_271, rawCapacityCrossLE_277, rawCapacityCrossLE_281]
  by_cases h301 : p ≤ 301
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_283, rawCapacityCrossLE_293]
  by_cases h321 : p ≤ 321
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_307, rawCapacityCrossLE_311, rawCapacityCrossLE_313, rawCapacityCrossLE_317]
  by_cases h341 : p ≤ 341
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_331, rawCapacityCrossLE_337]
  by_cases h361 : p ≤ 361
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_347, rawCapacityCrossLE_349, rawCapacityCrossLE_353, rawCapacityCrossLE_359]
  by_cases h381 : p ≤ 381
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_367, rawCapacityCrossLE_373, rawCapacityCrossLE_379]
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_383, rawCapacityCrossLE_389, rawCapacityCrossLE_397, rawCapacityCrossLE_401]

private theorem finitePrimeIndicatorListLoad_capacity {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ401 : ℓ ≤ 401) :
    finitePrimeIndicatorListLoad ℓ ≤
      C0Rat / (((ℓ - 1 : ℕ) : ℚ)) := by
  have hcross := rawCapacityCrossLE hℓ hℓ401
  have hle := RawFraction.toRat_le_of_crossLE
    (rawPrimeLoad_denominator_pos ℓ)
    (rawCapacity_denominator_pos hℓ.one_lt) hcross
  rw [rawPrimeLoad_toRat, rawCapacity_toRat hℓ.one_lt] at hle
  exact hle

theorem finiteAllocation_prime_capacity {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ401 : ℓ ≤ 401) :
    finitePrimeLoad ℓ ≤ C0Rat / (((ℓ - 1 : ℕ) : ℚ)) := by
  rw [finitePrimeLoad_eq_indicator]
  rw [finitePrimeIndicatorLoad_eq_list]
  exact finitePrimeIndicatorListLoad_capacity hℓ hℓ401

theorem previousPrime_spec {p : ℕ} (hp2 : 2 < p) :
    (previousPrime p).Prime ∧ previousPrime p < p ∧
      ∀ q, q.Prime → previousPrime p < q → q < p → False := by
  have htwo : 2 ≤ p - 1 := by omega
  have hprevPrime : (previousPrime p).Prime := by
    exact Nat.findGreatest_spec (P := Nat.Prime) htwo Nat.prime_two
  have hprevLe : previousPrime p ≤ p - 1 := by
    exact Nat.findGreatest_le (p - 1)
  refine ⟨hprevPrime, by omega, ?_⟩
  intro q hq hprevq hqp
  exact (Nat.findGreatest_is_greatest (P := Nat.Prime) hprevq (by omega)) hq


private theorem rawOverlapCrossLE {p : ℕ} (hp : p.Prime)
    (hp201 : 201 < p) (hp401 : p ≤ 401) :
    (RawFraction.add (rawPrimeLoad p) (rawTailOverlap p)).CrossLE
      (rawCapacity p) := by
  by_cases h221 : p ≤ 221
  · have hpEq : p = 211 := by
      interval_cases p <;> norm_num at hp
      rfl
    subst p
    exact rawOverlapCrossLE_211
  by_cases h241 : p ≤ 241
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_223, rawOverlapCrossLE_227, rawOverlapCrossLE_229, rawOverlapCrossLE_233, rawOverlapCrossLE_239, rawOverlapCrossLE_241]
  by_cases h261 : p ≤ 261
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_251, rawOverlapCrossLE_257]
  by_cases h281 : p ≤ 281
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_263, rawOverlapCrossLE_269, rawOverlapCrossLE_271, rawOverlapCrossLE_277, rawOverlapCrossLE_281]
  by_cases h301 : p ≤ 301
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_283, rawOverlapCrossLE_293]
  by_cases h321 : p ≤ 321
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_307, rawOverlapCrossLE_311, rawOverlapCrossLE_313, rawOverlapCrossLE_317]
  by_cases h341 : p ≤ 341
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_331, rawOverlapCrossLE_337]
  by_cases h361 : p ≤ 361
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_347, rawOverlapCrossLE_349, rawOverlapCrossLE_353, rawOverlapCrossLE_359]
  by_cases h381 : p ≤ 381
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_367, rawOverlapCrossLE_373, rawOverlapCrossLE_379]
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_383, rawOverlapCrossLE_389, rawOverlapCrossLE_397, rawOverlapCrossLE_401]

private theorem finitePrimeIndicatorListLoad_overlap {p : ℕ}
    (hp : p.Prime) (hp201 : 201 < p) (hp401 : p ≤ 401) :
    finitePrimeIndicatorListLoad p + finiteTailOverlap p ≤
      C0Rat / (((p - 1 : ℕ) : ℚ)) := by
  have hcross := rawOverlapCrossLE hp hp201 hp401
  have hle := RawFraction.toRat_le_of_crossLE
    (RawFraction.add_denominator_pos (rawPrimeLoad_denominator_pos p)
      (rawTailOverlap_denominator_pos p))
    (rawCapacity_denominator_pos hp.one_lt) hcross
  rw [RawFraction.toRat_add (rawPrimeLoad_denominator_pos p)
      (rawTailOverlap_denominator_pos p),
    rawPrimeLoad_toRat, rawTailOverlap_toRat hp201,
    rawCapacity_toRat hp.one_lt] at hle
  exact hle

theorem finiteAllocation_prime_overlap {p : ℕ} (hp : p.Prime)
    (hp201 : 201 < p) (hp401 : p ≤ 401) :
    finitePrimeLoad p +
        (∑ r ∈ Finset.Icc (max 201 (previousPrime p)) (p - 1), alpha r) ≤
      C0Rat / (((p - 1 : ℕ) : ℚ)) := by
  rw [finitePrimeLoad_eq_indicator]
  rw [finitePrimeIndicatorLoad_eq_list]
  change finitePrimeIndicatorListLoad p + finiteTailOverlap p ≤ _
  exact finitePrimeIndicatorListLoad_overlap hp hp201 hp401

/-! ## Literal paper-level certificate -/



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.Nagura -/
section


/-!
# A finite Nagura certificate and an asymptotic Nagura tail

Nagura's theorem says that every integer `n ≥ 25` has a prime `p` with
`n < p < 6n/5`.  The available assumption-free Mathlib theorem on explicit
prime intervals is Bertrand's postulate.  For the infinite tail we use the
assumption-free prime number theorem exported by `SafePrimeCounting`; the
stronger explicit results in the optional `PrimeNumberTheoremAnd` dependency
are not proof-complete and are deliberately not imported here.

This file proves the Nagura conclusion unconditionally on the complete
finite range `25 ≤ n < 91639`.  The certificate is a chain of actual primes;
successive entries `a,b` satisfy `5b < 6a`, so their covered integer
intervals overlap.  It also proves that the Nagura conclusion holds for all
sufficiently large integers and records the exact reduction of the full
theorem to a concrete tail, together with the transfer from a Nagura witness
to the ratio for consecutive primes.
-/

open Filter Topology

namespace Erdos390.WholePaper



/-- A kernel-checked finite Nagura certificate.  The upper endpoint exceeds
the cutoff `2103` in Nagura's original analytic proof. -/
theorem exists_prime_nagura_finite {n : ℕ} (hnLower : 25 ≤ n)
    (hnUpper : n < 2423) : HasNaguraPrime n := by
  by_cases h29 : n < 29
  · exact ⟨29, by norm_num, h29, by omega⟩
  by_cases h31 : n < 31
  · exact ⟨31, by norm_num, h31, by omega⟩
  by_cases h37 : n < 37
  · exact ⟨37, by norm_num, h37, by omega⟩
  by_cases h43 : n < 43
  · exact ⟨43, by norm_num, h43, by omega⟩
  by_cases h47 : n < 47
  · exact ⟨47, by norm_num, h47, by omega⟩
  by_cases h53 : n < 53
  · exact ⟨53, by norm_num, h53, by omega⟩
  by_cases h61 : n < 61
  · exact ⟨61, by norm_num, h61, by omega⟩
  by_cases h73 : n < 73
  · exact ⟨73, by norm_num, h73, by omega⟩
  by_cases h83 : n < 83
  · exact ⟨83, by norm_num, h83, by omega⟩
  by_cases h97 : n < 97
  · exact ⟨97, by norm_num, h97, by omega⟩
  by_cases h113 : n < 113
  · exact ⟨113, by norm_num, h113, by omega⟩
  by_cases h131 : n < 131
  · exact ⟨131, by norm_num, h131, by omega⟩
  by_cases h157 : n < 157
  · exact ⟨157, by norm_num, h157, by omega⟩
  by_cases h181 : n < 181
  · exact ⟨181, by norm_num, h181, by omega⟩
  by_cases h211 : n < 211
  · exact ⟨211, by norm_num, h211, by omega⟩
  by_cases h251 : n < 251
  · exact ⟨251, by norm_num, h251, by omega⟩
  by_cases h293 : n < 293
  · exact ⟨293, by norm_num, h293, by omega⟩
  by_cases h349 : n < 349
  · exact ⟨349, by norm_num, h349, by omega⟩
  by_cases h409 : n < 409
  · exact ⟨409, by norm_num, h409, by omega⟩
  by_cases h487 : n < 487
  · exact ⟨487, by norm_num, h487, by omega⟩
  by_cases h577 : n < 577
  · exact ⟨577, by norm_num, h577, by omega⟩
  by_cases h691 : n < 691
  · exact ⟨691, by norm_num, h691, by omega⟩
  by_cases h829 : n < 829
  · exact ⟨829, by norm_num, h829, by omega⟩
  by_cases h991 : n < 991
  · exact ⟨991, by norm_num, h991, by omega⟩
  by_cases h1187 : n < 1187
  · exact ⟨1187, by norm_num, h1187, by omega⟩
  by_cases h1423 : n < 1423
  · exact ⟨1423, by norm_num, h1423, by omega⟩
  by_cases h1699 : n < 1699
  · exact ⟨1699, by norm_num, h1699, by omega⟩
  by_cases h2029 : n < 2029
  · exact ⟨2029, by norm_num, h2029, by omega⟩
  exact ⟨2423, by norm_num, hnUpper, by omega⟩

/-- A second kernel-checked prime chain bridges the original finite
certificate past `89693`, the threshold in Dusart's explicit interval
estimate.  No result from the incomplete Dusart module is imported. -/
theorem exists_prime_nagura_medium {n : ℕ} (hnLower : 2423 ≤ n)
    (hnUpper : n < 91639) : HasNaguraPrime n := by
  by_cases h2903 : n < 2903
  · exact ⟨2903, by norm_num, h2903, by omega⟩
  by_cases h3469 : n < 3469
  · exact ⟨3469, by norm_num, h3469, by omega⟩
  by_cases h4159 : n < 4159
  · exact ⟨4159, by norm_num, h4159, by omega⟩
  by_cases h4987 : n < 4987
  · exact ⟨4987, by norm_num, h4987, by omega⟩
  by_cases h5981 : n < 5981
  · exact ⟨5981, by norm_num, h5981, by omega⟩
  by_cases h7177 : n < 7177
  · exact ⟨7177, by norm_num, h7177, by omega⟩
  by_cases h8609 : n < 8609
  · exact ⟨8609, by norm_num, h8609, by omega⟩
  by_cases h10321 : n < 10321
  · exact ⟨10321, by norm_num, h10321, by omega⟩
  by_cases h12379 : n < 12379
  · exact ⟨12379, by norm_num, h12379, by omega⟩
  by_cases h14851 : n < 14851
  · exact ⟨14851, by norm_num, h14851, by omega⟩
  by_cases h17807 : n < 17807
  · exact ⟨17807, by norm_num, h17807, by omega⟩
  by_cases h21347 : n < 21347
  · exact ⟨21347, by norm_num, h21347, by omega⟩
  by_cases h25609 : n < 25609
  · exact ⟨25609, by norm_num, h25609, by omega⟩
  by_cases h30727 : n < 30727
  · exact ⟨30727, by norm_num, h30727, by omega⟩
  by_cases h36871 : n < 36871
  · exact ⟨36871, by norm_num, h36871, by omega⟩
  by_cases h44221 : n < 44221
  · exact ⟨44221, by norm_num, h44221, by omega⟩
  by_cases h53051 : n < 53051
  · exact ⟨53051, by norm_num, h53051, by omega⟩
  by_cases h63659 : n < 63659
  · exact ⟨63659, by norm_num, h63659, by omega⟩
  by_cases h76387 : n < 76387
  · exact ⟨76387, by norm_num, h76387, by omega⟩
  exact ⟨91639, by norm_num, hnUpper, by omega⟩

/-- Combined unconditional certificate through the explicit-estimate
threshold. -/
theorem exists_prime_nagura_below_91639 {n : ℕ} (hnLower : 25 ≤ n)
    (hnUpper : n < 91639) : HasNaguraPrime n := by
  by_cases h : n < 2423
  · exact exists_prime_nagura_finite hnLower h
  · exact exists_prime_nagura_medium (by omega) hnUpper











/-- A Nagura witness above `pPrev`, together with the assertion that `p` is
the least prime above `pPrev`, gives the scalar inequality used in the
allocation tail. -/
theorem consecutivePrime_ratio_of_naguraWitness {pPrev p : ℕ}
    (hLeast : ∀ q : ℕ, q.Prime → pPrev < q → p ≤ q)
    (hNagura : HasNaguraPrime pPrev) :
    5 * p < 6 * pPrev := by
  obtain ⟨q, hqPrime, hPrevQ, hqRatio⟩ := hNagura
  have hpq : p ≤ q := hLeast q hqPrime hPrevQ
  omega



end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.LeastPrimeTail -/
section


/-! # Least-prime routing for the infinite allocation tail -/

namespace Erdos390.WholePaper

noncomputable section





theorem leastPrimeAbove_prime (n : ℕ) : (leastPrimeAbove n).Prime :=
  (Nat.find_spec (exists_prime_strictly_above n)).1









/-- For consecutive primes `pPrev < p`, least-prime routing sends exactly
the integer block `pPrev ≤ r ≤ p-1` to `p`. -/
theorem leastPrimeAbove_eq_of_consecutivePrimes
    {pPrev p r : ℕ} (hpPrev : pPrev.Prime) (hp : p.Prime)
    (hPrevP : pPrev < p)
    (hNoBetween : ∀ q : ℕ, q.Prime → pPrev < q → q < p → False) :
    leastPrimeAbove r = p ↔ pPrev ≤ r ∧ r < p := by
  constructor
  · intro hleast
    constructor
    · by_contra hPrevR
      have hrPrev : r < pPrev := by omega
      have hle : leastPrimeAbove r ≤ pPrev :=
        leastPrimeAbove_le hpPrev hrPrev
      omega
    · simpa only [hleast] using lt_leastPrimeAbove r
  · rintro ⟨hPrevR, hrP⟩
    apply Nat.le_antisymm (leastPrimeAbove_le hp hrP)
    by_contra hnot
    have hleastLt : leastPrimeAbove r < p := by omega
    exact hNoBetween (leastPrimeAbove r) (leastPrimeAbove_prime r)
      (hPrevR.trans_lt (lt_leastPrimeAbove r)) hleastLt

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.InfiniteAllocationTailCore -/
section


/-!
# Finite-support algebra for the least-prime allocation tail

This module contains the part of Lemma 4.2 that is independent of the
large finite certificate.  Keeping that certificate out of this import
chain materially reduces elaboration memory for the reusable tail lemmas.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section













/-- A tail row contributes only to the prime selected by its least-prime
route. -/
theorem tailPrimeRowLoad_eq (ℓ r : ℕ) :
    tailPrimeRowLoad ℓ r =
      if 201 ≤ r ∧ leastPrimeAbove r = ℓ then alpha r else 0 := by
  classical
  by_cases hr : 201 ≤ r
  · have hr1 : 1 ≤ r := by omega
    have hleastMem := leastPrimeAbove_mem_allocationRange hr1
    rw [tailPrimeRowLoad, allocationPrimeRowLoad]
    calc
      (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
          (q.factorization ℓ : ℚ) * tailAllocation r q) =
          ((leastPrimeAbove r).factorization ℓ : ℚ) * alpha r := by
        rw [Finset.sum_eq_single (leastPrimeAbove r)]
        · simp [tailAllocation, hr]
        · intro q _hq hqne
          simp [tailAllocation, hqne]
        · exact fun hnot ↦ (hnot hleastMem).elim
      _ = if 201 ≤ r ∧ leastPrimeAbove r = ℓ then alpha r else 0 := by
        rw [(leastPrimeAbove_prime r).factorization]
        by_cases hℓ : leastPrimeAbove r = ℓ
        · simp [hr, hℓ]
        · simp [hr, hℓ]
  · simp [tailPrimeRowLoad, allocationPrimeRowLoad, tailAllocation, hr]

/-- For a fixed prime coordinate, all tail rows outside
`[201, ℓ - 1]` vanish. -/
theorem tsum_tailPrimeRowLoad_eq (ℓ : ℕ) :
    (∑' r : ℕ, tailPrimeRowLoad ℓ r) =
      ∑ r ∈ Finset.Icc 201 (ℓ - 1),
        if leastPrimeAbove r = ℓ then alpha r else 0 := by
  rw [tsum_eq_sum (s := Finset.Icc 201 (ℓ - 1))]
  · apply Finset.sum_congr rfl
    intro r hr
    have hr201 := (Finset.mem_Icc.mp hr).1
    rw [tailPrimeRowLoad_eq]
    simp [hr201]
  · intro r hr
    rw [tailPrimeRowLoad_eq]
    by_cases hr201 : 201 ≤ r
    · have hroute : leastPrimeAbove r ≠ ℓ := by
        intro hroute
        apply hr
        exact Finset.mem_Icc.mpr ⟨hr201, by
          have := lt_leastPrimeAbove r
          omega⟩
      simp [hr201, hroute]
    · simp [hr201]

theorem summable_tailPrimeRowLoad (ℓ : ℕ) :
    Summable (tailPrimeRowLoad ℓ) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 201 (ℓ - 1))
  intro r hr
  rw [tailPrimeRowLoad_eq]
  by_cases hr201 : 201 ≤ r
  · have hroute : leastPrimeAbove r ≠ ℓ := by
      intro hroute
      apply hr
      exact Finset.mem_Icc.mpr ⟨hr201, by
        have := lt_leastPrimeAbove r
        omega⟩
    simp [hr201, hroute]
  · simp [hr201]

/-- Consecutive-prime routing turns the tail `tsum` into the literal block
used by the finite overlap certificate and the Nagura estimate. -/
theorem tsum_tailPrimeRowLoad_eq_consecutiveBlock
    {pPrev p : ℕ} (hpPrev : pPrev.Prime) (hp : p.Prime)
    (hPrevP : pPrev < p)
    (hNoBetween : ∀ q : ℕ, q.Prime → pPrev < q → q < p → False) :
    (∑' r : ℕ, tailPrimeRowLoad p r) =
      ∑ r ∈ Finset.Icc (max 201 pPrev) (p - 1), alpha r := by
  rw [tsum_tailPrimeRowLoad_eq]
  have hfilter :
      (Finset.Icc 201 (p - 1)).filter
          (fun r ↦ leastPrimeAbove r = p) =
        Finset.Icc (max 201 pPrev) (p - 1) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc,
      leastPrimeAbove_eq_of_consecutivePrimes hpPrev hp hPrevP hNoBetween]
    omega
  have hsum := congrArg (fun s : Finset ℕ ↦ ∑ r ∈ s, alpha r) hfilter
  simpa only [Finset.sum_filter] using hsum

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.InfiniteAllocationCore -/
section


/-!
# The exact infinite cofactor array: structural layer

This file splices the 200 finite certificate rows to the least-prime tail.
It proves nonnegativity, the permitted cofactor support, every exact row
identity, and finite-support formulas for each prime load.  The capacity
inequalities are instantiated in `InfiniteAllocation.lean`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section














/-- The finite part of a fixed prime load is literally the checked finite
certificate load. -/
theorem tsum_finitePrimeRowLoad_eq ( ℓ : ℕ) :
    (∑' r : ℕ, finitePrimeRowLoad ℓ r) = finitePrimeLoad ℓ := by
  rw [tsum_eq_sum (s := Finset.Icc 1 200)]
  · exact (finitePrimeLoad_eq_coordinate_sum ℓ).symm
  · intro r hr
    rw [finitePrimeRowLoad, allocationPrimeRowLoad]
    apply Finset.sum_eq_zero
    intro q _hq
    rw [finiteAllocation_eq_zero_of_not_mem]
    · simp
    · intro hrq
      exact hr (Finset.mem_Icc.mpr
        ⟨(finiteAllocation_support_valid hrq).1,
          (finiteAllocation_support_valid hrq).2.1⟩)

theorem summable_finitePrimeRowLoad (ℓ : ℕ) :
    Summable (finitePrimeRowLoad ℓ) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 200)
  intro r hr
  rw [finitePrimeRowLoad, allocationPrimeRowLoad]
  apply Finset.sum_eq_zero
  intro q _hq
  rw [finiteAllocation_eq_zero_of_not_mem]
  · simp
  · intro hrq
    exact hr (Finset.mem_Icc.mpr
      ⟨(finiteAllocation_support_valid hrq).1,
        (finiteAllocation_support_valid hrq).2.1⟩)

theorem infinitePrimeRowLoad_eq_add (ℓ r : ℕ) :
    allocationPrimeRowLoad infiniteAllocation ℓ r =
      finitePrimeRowLoad ℓ r + tailPrimeRowLoad ℓ r := by
  simp only [allocationPrimeRowLoad, finitePrimeRowLoad, tailPrimeRowLoad,
    infiniteAllocation, mul_add, Finset.sum_add_distrib]

/-- The full load splits exactly into the finite certificate load and the
least-prime tail load. -/
theorem allocationPrimeLoad_infiniteAllocation_eq (ℓ : ℕ) :
    allocationPrimeLoad infiniteAllocation ℓ =
      finitePrimeLoad ℓ + ∑' r : ℕ, tailPrimeRowLoad ℓ r := by
  rw [allocationPrimeLoad]
  simp_rw [infinitePrimeRowLoad_eq_add]
  rw [(summable_finitePrimeRowLoad ℓ).tsum_add
      (summable_tailPrimeRowLoad ℓ),
    tsum_finitePrimeRowLoad_eq]

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.AllocationTailCapacity -/
section


/-! # Exact capacity estimate for one least-prime allocation block -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

theorem alpha_lt_one_div_two_mul_sq {a r : ℕ}
    (ha : 0 < a) (har : a ≤ r) :
    alpha r < 1 / (2 * (a : ℚ) ^ 2) := by
  rw [alpha]
  apply one_div_lt_one_div_of_lt
  · positivity
  · have haR : (0 : ℚ) < a := by exact_mod_cast ha
    have harR : (a : ℚ) ≤ r := by exact_mod_cast har
    have hsq : (a : ℚ) ^ 2 ≤ (r : ℚ) ^ 2 := by
      exact (sq_le_sq₀ haR.le (Nat.cast_nonneg r)).2 harR
    calc
      2 * (a : ℚ) ^ 2 ≤ 2 * (r : ℚ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ < ((r : ℚ) + 1) * (2 * (r : ℚ) + 1) := by
        rw [show ((r : ℚ) + 1) * (2 * (r : ℚ) + 1) =
            2 * (r : ℚ) ^ 2 + (3 * (r : ℚ) + 1) by ring]
        exact lt_add_of_pos_right _ (by positivity)

theorem allocationTail_alpha_block_sum_lt
    {a p : ℕ} (ha : 0 < a) (hap : a < p) :
    (∑ r ∈ Finset.Icc a (p - 1), alpha r) <
      ((p - a : ℕ) : ℚ) / (2 * (a : ℚ) ^ 2) := by
  let rows := Finset.Icc a (p - 1)
  have haMem : a ∈ rows := by
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hsum :
      (∑ r ∈ rows, alpha r) <
        ∑ _r ∈ rows, (1 / (2 * (a : ℚ) ^ 2)) := by
    exact Finset.sum_lt_sum_of_nonempty ⟨a, haMem⟩ fun r hr ↦
      alpha_lt_one_div_two_mul_sq ha (Finset.mem_Icc.mp hr).1
  have hcard : rows.card = p - a := by
    dsimp only [rows]
    rw [Nat.card_Icc]
    omega
  have hconst :
      (∑ _r ∈ rows, (1 / (2 * (a : ℚ) ^ 2))) =
        (rows.card : ℚ) * (1 / (2 * (a : ℚ) ^ 2)) := by
    simp
  rw [hconst, hcard] at hsum
  simpa only [rows, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv,
    one_mul] using hsum

theorem nagura_gap_fraction_lt_three_div_twenty_five
    {a p : ℕ} (ha : 0 < a) (hap : a < p)
    (hNagura : 5 * p < 6 * a) :
    (p : ℚ) * ((p - a : ℕ) : ℚ) /
        (2 * (a : ℚ) ^ 2) <
      (3 : ℚ) / 25 := by
  have haR : (0 : ℚ) < a := by exact_mod_cast ha
  have hapR : (a : ℚ) < p := by exact_mod_cast hap
  have hNaguraR : (5 : ℚ) * p < 6 * a := by exact_mod_cast hNagura
  have hsubCast : (((p - a : ℕ) : ℚ)) = (p : ℚ) - a := by
    rw [Nat.cast_sub hap.le]
  rw [hsubCast]
  have hpPos : (0 : ℚ) < p := haR.trans hapR
  have hgapPos : (0 : ℚ) < (p : ℚ) - a := sub_pos.mpr hapR
  have hpBound : (p : ℚ) < (6 / 5 : ℚ) * a := by
    linarith
  have hgapBound : (p : ℚ) - a < (1 / 5 : ℚ) * a := by
    linarith
  have hproduct :
      (p : ℚ) * ((p : ℚ) - a) <
        ((6 / 5 : ℚ) * a) * ((1 / 5 : ℚ) * a) :=
    mul_lt_mul hpBound hgapBound.le hgapPos
      (by positivity)
  have hdenom : (0 : ℚ) < 2 * (a : ℚ) ^ 2 := by positivity
  apply (div_lt_iff₀ hdenom).2
  calc
    (p : ℚ) * ((p : ℚ) - a) <
        ((6 / 5 : ℚ) * a) * ((1 / 5 : ℚ) * a) := hproduct
    _ = (3 / 25 : ℚ) * (2 * (a : ℚ) ^ 2) := by ring

/-- The exact strict capacity estimate used for every tail prime above the
finite certificate. -/
theorem allocationTail_block_capacity_lt_C0Rat
    {pPrev p : ℕ} (hpPrevPos : 0 < pPrev) (hPrevP : pPrev < p)
    (hNagura : 5 * p < 6 * pPrev) :
    (((p - 1 : ℕ) : ℚ)) *
        (∑ r ∈ Finset.Icc pPrev (p - 1), alpha r) < C0Rat := by
  have hsum := allocationTail_alpha_block_sum_lt hpPrevPos hPrevP
  have hpPredLt : ((p - 1 : ℕ) : ℚ) < (p : ℚ) := by
    exact_mod_cast Nat.pred_lt (Nat.ne_of_gt (hpPrevPos.trans hPrevP))
  have hscaled := mul_lt_mul_of_pos_left hsum
    (show (0 : ℚ) < (p - 1 : ℕ) by
      exact_mod_cast (by omega : 0 < p - 1))
  have hquotPos :
      (0 : ℚ) < ((p - pPrev : ℕ) : ℚ) /
        (2 * (pPrev : ℚ) ^ 2) := by
    apply div_pos
    · exact_mod_cast Nat.sub_pos_of_lt hPrevP
    · positivity
  have hreplace :
      ((p - 1 : ℕ) : ℚ) *
          (((p - pPrev : ℕ) : ℚ) /
            (2 * (pPrev : ℚ) ^ 2)) <
        (p : ℚ) * ((p - pPrev : ℕ) : ℚ) /
          (2 * (pPrev : ℚ) ^ 2) := by
    calc
      ((p - 1 : ℕ) : ℚ) *
          (((p - pPrev : ℕ) : ℚ) /
            (2 * (pPrev : ℚ) ^ 2)) <
          (p : ℚ) *
            (((p - pPrev : ℕ) : ℚ) /
              (2 * (pPrev : ℚ) ^ 2)) :=
        mul_lt_mul_of_pos_right hpPredLt hquotPos
      _ = (p : ℚ) * ((p - pPrev : ℕ) : ℚ) /
          (2 * (pPrev : ℚ) ^ 2) := by ring
  have hthree := nagura_gap_fraction_lt_three_div_twenty_five
    hpPrevPos hPrevP hNagura
  exact (((hscaled.trans hreplace).trans hthree).trans
    three_div_twenty_five_lt_C0Rat)

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraChebyshevIdentity -/
section


/-!
# The finite divisor identity behind Nagura's Chebyshev sum

Nagura's fundamental summatory formula starts by expanding each logarithm as
a divisor sum of the von Mangoldt function.  This file records that exact
finite identity, including the factorial endpoint, independently of any
analytic estimate.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open scoped ArithmeticFunction ArithmeticFunction.zeta



/-- Dirichlet-convolution form of Nagura's fundamental finite identity. -/
theorem naguraChebyshevSum_eq_sum_log (n : ℕ) :
    naguraChebyshevSum n =
      ∑ k ∈ Finset.Icc 1 n, Real.log k := by
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (R := ℝ)
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    ArithmeticFunction.vonMangoldt n
  have hMain :
      (∑ m ∈ Finset.Ioc 0 n,
        ∑ d ∈ Finset.Ioc 0 (n / m),
          ArithmeticFunction.vonMangoldt d) =
        ∑ k ∈ Finset.Ioc 0 n, Real.log k := by
    calc
      _ = ∑ m ∈ Finset.Ioc 0 n,
          (if m = 0 then 0 else
            ∑ d ∈ Finset.Ioc 0 (n / m),
              ArithmeticFunction.vonMangoldt d) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm0 : m ≠ 0 := by
          have := (Finset.mem_Ioc.mp hm).1
          omega
        simp [hm0]
      _ = _ := by
        simpa [ArithmeticFunction.log_apply] using h.symm
  have hIntervals : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hIntervals]
  simpa [naguraChebyshevSum, Chebyshev.psi] using hMain



theorem naguraDivisorLogSum_eq_sum_log (n : ℕ) :
    naguraDivisorLogSum n = ∑ k ∈ Finset.Icc 1 n, Real.log k := by
  unfold naguraDivisorLogSum
  apply Finset.sum_congr rfl
  intro k _hk
  exact ArithmeticFunction.vonMangoldt_sum

/-- Exact factorial form of the finite divisor identity. -/
theorem naguraDivisorLogSum_eq_log_factorial (n : ℕ) :
    naguraDivisorLogSum n = Real.log (n.factorial : ℝ) := by
  rw [naguraDivisorLogSum_eq_sum_log]
  calc
    (∑ k ∈ Finset.Icc 1 n, Real.log k) =
        Real.log (∏ k ∈ Finset.Icc 1 n, (k : ℝ)) := by
      rw [Real.log_prod]
      intro k hk
      have hk0 : k ≠ 0 := by
        have := (Finset.mem_Icc.mp hk).1
        omega
      exact_mod_cast hk0
    _ = Real.log (n.factorial : ℝ) := by
      congr 1
      rw [← Nat.cast_prod]
      norm_cast
      rw [← Finset.Ico_add_one_right_eq_Icc,
        Finset.prod_Ico_id_eq_factorial]

/-- Exact natural-endpoint version of Nagura's fundamental formula. -/
theorem naguraChebyshevSum_eq_log_factorial (n : ℕ) :
    naguraChebyshevSum n = Real.log (n.factorial : ℝ) := by
  rw [naguraChebyshevSum_eq_sum_log]
  exact (naguraDivisorLogSum_eq_sum_log n).symm.trans
    (naguraDivisorLogSum_eq_log_factorial n)

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraFactorialBounds -/
section


/-!
# Effective factorial bounds for Nagura's Chebyshev sum

The exact identity `naguraChebyshevSum_eq_log_factorial` reduces analytic
bounds for Nagura's `T` function to explicit estimates for `log (n!)`.  This
file records the elementary integral upper bound, complementing Mathlib's
global Stirling lower bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

/-- Elementary global upper bound for the factorial logarithm. -/
theorem log_factorial_le_integral_upper (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) -
        ((n + 1 : ℕ) : ℝ) + 1 := by
  have hIntegral := MonotoneOn.sum_le_integral_Ico
    (f := Real.log) (a := 1) (b := n + 1) (by omega) (by
      intro x hx y _ hxy
      exact Real.log_le_log (lt_of_lt_of_le (by norm_num) hx.1) hxy)
  have hSum :
      (∑ k ∈ Finset.Ico 1 (n + 1), Real.log k) =
        Real.log (n.factorial : ℝ) := by
    rw [Finset.Ico_add_one_right_eq_Icc]
    exact (naguraDivisorLogSum_eq_sum_log n).symm.trans
      (naguraDivisorLogSum_eq_log_factorial n)
  rw [hSum, integral_log] at hIntegral
  simpa using hIntegral



/-- The same elementary estimate, written in the form used in Nagura's
linear combination of factorial logarithms. -/
theorem log_factorial_le_stirling_elementary {n : ℕ} (hn : n ≠ 0) :
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
        Real.log (n : ℝ) + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h := log_factorial_le_integral_upper m
  rw [Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity)]
  linarith



end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraStirlingCombination -/
section


/-!
# Nagura's explicit Stirling combination

Nagura uses the reciprocal identity

`1 / 2 + 1 / 3 + 1 / 7 + 1 / 43 + 1 / 1806 = 1`

to combine six values of his finite Chebyshev sum.  This file records the
analytic half of that argument: the positive term is bounded by the elementary
factorial estimate, and the five subtracted terms are bounded with Mathlib's
proved Stirling lower bound.
-/

namespace Erdos390.WholePaper















/-- Mathlib's Stirling theorem supplies the lower model for every positive
factorial argument. -/
theorem naguraFactorialLogLower_le_log_factorial {n : ℕ} (hn : n ≠ 0) :
    naguraFactorialLogLower n ≤ Real.log (n.factorial : ℝ) := by
  exact Stirling.le_log_factorial_stirling hn

/-- The elementary integral estimate supplies the upper model. -/
theorem log_factorial_le_naguraFactorialLogUpper {n : ℕ} (hn : n ≠ 0) :
    Real.log (n.factorial : ℝ) ≤ naguraFactorialLogUpper n := by
  exact log_factorial_le_stirling_elementary hn





end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraLogBounds -/
section


/-!
# Certified logarithm bounds used by Nagura

The only transcendental numerical input below is Mathlib's proved
`Real.log_two_lt_d9`.  The remaining logarithms are reduced to powers of two
and bounded by the explicit finite Taylor remainder theorem for
`log (1 - x)`.  Every residual calculation is rational and discharged by
`norm_num`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

/-- A convenient one-sided form of Mathlib's finite Taylor remainder bound
for `log (1 - x)`. -/
theorem log_one_sub_le_neg_sum_add_remainder {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    Real.log (1 - x) ≤
      -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) +
        |x| ^ (n + 1) / (1 - |x|) := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  have hUpper := (abs_le.mp h).2
  linarith

theorem log_three_lt_1_099 :
    Real.log 3 < (1099 : ℝ) / 1000 := by
  have hResidual :
      Real.log (1 - (1 : ℝ) / 4) ≤ -(2873 : ℝ) / 10000 := by
    calc
      Real.log (1 - (1 : ℝ) / 4) ≤
          -(∑ i ∈ Finset.range 5,
              ((1 : ℝ) / 4) ^ (i + 1) / (i + 1)) +
            |(1 : ℝ) / 4| ^ (5 + 1) / (1 - |(1 : ℝ) / 4|) :=
        log_one_sub_le_neg_sum_add_remainder (by norm_num) 5
      _ ≤ -(2873 : ℝ) / 10000 := by
        norm_num [Finset.sum_range_succ]
  have hSplit :
      Real.log 3 = 2 * Real.log 2 + Real.log (1 - (1 : ℝ) / 4) := by
    calc
      Real.log 3 = Real.log ((2 : ℝ) ^ 2 * (1 - (1 : ℝ) / 4)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 2) + Real.log (1 - (1 : ℝ) / 4) := by
        rw [Real.log_mul] <;> norm_num
      _ = 2 * Real.log 2 + Real.log (1 - (1 : ℝ) / 4) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_lt_d9]







theorem log_forty_three_lt_3_762 :
    Real.log 43 < (1881 : ℝ) / 500 := by
  have hResidual :
      Real.log (1 - (21 : ℝ) / 64) ≤ -(3969 : ℝ) / 10000 := by
    calc
      Real.log (1 - (21 : ℝ) / 64) ≤
          -(∑ i ∈ Finset.range 6,
              ((21 : ℝ) / 64) ^ (i + 1) / (i + 1)) +
            |(21 : ℝ) / 64| ^ (6 + 1) / (1 - |(21 : ℝ) / 64|) :=
        log_one_sub_le_neg_sum_add_remainder (by norm_num) 6
      _ ≤ -(3969 : ℝ) / 10000 := by
        norm_num [Finset.sum_range_succ]
  have hSplit :
      Real.log 43 = 6 * Real.log 2 + Real.log (1 - (21 : ℝ) / 64) := by
    calc
      Real.log 43 = Real.log ((2 : ℝ) ^ 6 * (1 - (21 : ℝ) / 64)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 6) + Real.log (1 - (21 : ℝ) / 64) := by
        rw [Real.log_mul] <;> norm_num
      _ = 6 * Real.log 2 + Real.log (1 - (21 : ℝ) / 64) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_lt_d9]



theorem log_one_thousand_eight_hundred_six_lt_seven_point_five :
    Real.log 1806 < (15 : ℝ) / 2 := by
  have hResidual :
      Real.log (1 - (121 : ℝ) / 1024) ≤ -(1254 : ℝ) / 10000 := by
    calc
      Real.log (1 - (121 : ℝ) / 1024) ≤
          -(∑ i ∈ Finset.range 3,
              ((121 : ℝ) / 1024) ^ (i + 1) / (i + 1)) +
            |(121 : ℝ) / 1024| ^ (3 + 1) /
              (1 - |(121 : ℝ) / 1024|) :=
        log_one_sub_le_neg_sum_add_remainder (by norm_num) 3
      _ ≤ -(1254 : ℝ) / 10000 := by
        norm_num [Finset.sum_range_succ]
  have hSplit :
      Real.log 1806 =
        11 * Real.log 2 + Real.log (1 - (121 : ℝ) / 1024) := by
    calc
      Real.log 1806 =
          Real.log ((2 : ℝ) ^ 11 * (1 - (121 : ℝ) / 1024)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 11) +
          Real.log (1 - (121 : ℝ) / 1024) := by
        rw [Real.log_mul] <;> norm_num
      _ = 11 * Real.log 2 + Real.log (1 - (121 : ℝ) / 1024) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_lt_d9]















end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraCombinatorial -/
section


/-!
# The combinatorial half of Nagura's Chebyshev argument

This file expands Nagura's six-term `T` combination into a weighted sum of a
decreasing sequence.  Its prefix weights are explicit floor expressions, so a
finite summation-by-parts identity gives the required lower bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

/-- Shift a sum over the positive natural interval `1, ..., n` to a zero-based
range. -/
theorem sum_Ioc_zero_eq_sum_range_succ {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (n : ℕ) :
    (∑ m ∈ Finset.Ioc 0 n, f m) = ∑ i ∈ Finset.range n, f (i + 1) := by
  rw [show Finset.Ioc 0 n = Finset.Ico 1 (n + 1) by ext m; simp; omega,
    Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

/-- There are exactly `n / d` positive multiples of a positive `d` among
`1, ..., n`, expressed as a sum of indicators. -/
theorem sum_dvd_indicator_eq_div (d : ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range n, if d ∣ i + 1 then (1 : ℝ) else 0) = (n / d : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h : d ∣ n + 1
      · rw [if_pos h, Nat.succ_div_of_dvd h]
        norm_num
      · rw [if_neg h, Nat.succ_div_of_not_dvd h]
        norm_num

/-- Indicator selection of the positive multiples of `d`. -/
theorem sum_dvd_indicator_apply_eq (d : ℕ)
    (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, if d ∣ i + 1 then f (i + 1) else 0) =
      ∑ j ∈ Finset.range (n / d), f (d * (j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases h : d ∣ n + 1
      · rw [if_pos h, Nat.succ_div_of_dvd h, Finset.sum_range_succ]
        congr 1
        apply congrArg f
        have hCancel : (n + 1) / d * d = n + 1 := Nat.div_mul_cancel h
        have hQuot : (n + 1) / d = n / d + 1 := Nat.succ_div_of_dvd h
        calc
          n + 1 = (n + 1) / d * d := hCancel.symm
          _ = d * ((n + 1) / d) := Nat.mul_comm _ _
          _ = d * (n / d + 1) := by rw [hQuot]
      · rw [if_neg h, Nat.succ_div_of_not_dvd h]
        simp

/-- A finite summation-by-parts identity, written in terms of inclusive
partial sums. -/
theorem sum_range_mul_eq_partial_sum
    (c a : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), c i * a i) =
      (∑ j ∈ Finset.range (n + 1), c j) * a n +
        ∑ i ∈ Finset.range n,
          (∑ j ∈ Finset.range (i + 1), c j) * (a i - a (i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hPrefix :
          (∑ j ∈ Finset.range (n + 1 + 1), c j) =
            (∑ j ∈ Finset.range (n + 1), c j) + c (n + 1) :=
        Finset.sum_range_succ c (n + 1)
      have hDiff :
          (∑ i ∈ Finset.range (n + 1),
              (∑ j ∈ Finset.range (i + 1), c j) * (a i - a (i + 1))) =
            (∑ i ∈ Finset.range n,
              (∑ j ∈ Finset.range (i + 1), c j) * (a i - a (i + 1))) +
              (∑ j ∈ Finset.range (n + 1), c j) *
                (a n - a (n + 1)) :=
        Finset.sum_range_succ _ n
      calc
        (∑ i ∈ Finset.range (n + 1 + 1), c i * a i) =
            (∑ i ∈ Finset.range (n + 1), c i * a i) +
              c (n + 1) * a (n + 1) := Finset.sum_range_succ _ (n + 1)
        _ = ((∑ j ∈ Finset.range (n + 1), c j) * a n +
              ∑ i ∈ Finset.range n,
                (∑ j ∈ Finset.range (i + 1), c j) * (a i - a (i + 1))) +
              c (n + 1) * a (n + 1) := by rw [ih]
        _ = (∑ j ∈ Finset.range (n + 1 + 1), c j) * a (n + 1) +
              ∑ i ∈ Finset.range (n + 1),
                (∑ j ∈ Finset.range (i + 1), c j) * (a i - a (i + 1)) := by
          rw [hPrefix, hDiff]
          ring





theorem sum_naguraWeight_eq_prefix (m : ℕ) :
    (∑ i ∈ Finset.range m, naguraWeight (i + 1)) = naguraWeightPrefix m := by
  simp only [naguraWeight, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  rw [sum_dvd_indicator_eq_div 2,
    sum_dvd_indicator_eq_div 3,
    sum_dvd_indicator_eq_div 7,
    sum_dvd_indicator_eq_div 43,
    sum_dvd_indicator_eq_div 1806]
  rfl

/-- Every prefix sum of Nagura's weights is nonnegative.  This is the exact
integer content of the reciprocal identity. -/
theorem naguraWeightPrefix_nonneg (m : ℕ) :
    0 ≤ naguraWeightPrefix m := by
  let q := m / 2 + m / 3 + m / 7 + m / 43 + m / 1806
  have h2 := Nat.div_mul_le_self m 2
  have h3 := Nat.div_mul_le_self m 3
  have h7 := Nat.div_mul_le_self m 7
  have h43 := Nat.div_mul_le_self m 43
  have h1806 := Nat.div_mul_le_self m 1806
  have hq : q ≤ m := by
    dsimp only [q]
    omega
  have hqR : (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hq
  dsimp only [q] at hqR
  push_cast at hqR
  unfold naguraWeightPrefix
  linarith

/-- Before the first complete `1806`-block, every nonempty prefix sum is at
least one. -/
theorem one_le_naguraWeightPrefix {m : ℕ} (hm : 0 < m) (hm1806 : m < 1806) :
    1 ≤ naguraWeightPrefix m := by
  let q := m / 2 + m / 3 + m / 7 + m / 43
  have h2 := Nat.div_mul_le_self m 2
  have h3 := Nat.div_mul_le_self m 3
  have h7 := Nat.div_mul_le_self m 7
  have h43 := Nat.div_mul_le_self m 43
  have hq : q < m := by
    dsimp only [q]
    omega
  have hqR : (q : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hq
  dsimp only [q] at hqR
  push_cast at hqR
  unfold naguraWeightPrefix
  rw [Nat.div_eq_of_lt hm1806]
  norm_num
  linarith

/-- The abstract decreasing-sequence inequality behind Nagura's choice of
denominators.  The right side uses at least one full `1806`-block. -/
theorem first_sub_1806_le_nagura_weighted_sum
    (a : ℕ → ℝ) (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i)
    {N : ℕ} (hN : 1806 ≤ N) :
    a 0 - a 1805 ≤
      ∑ i ∈ Finset.range N, naguraWeight (i + 1) * a i := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hM : 1805 ≤ M := by omega
  let c : ℕ → ℝ := fun i ↦ naguraWeight (i + 1)
  let P : ℕ → ℝ := fun i ↦ ∑ j ∈ Finset.range (i + 1), c j
  have hP (i : ℕ) : P i = naguraWeightPrefix (i + 1) := by
    exact sum_naguraWeight_eq_prefix (i + 1)
  have hP0 (i : ℕ) : 0 ≤ P i := by
    rw [hP]
    exact naguraWeightPrefix_nonneg (i + 1)
  have hDiff (i : ℕ) : 0 ≤ a i - a (i + 1) := by
    exact sub_nonneg.mpr (ha (Nat.le_succ i))
  have hInitial :
      (∑ i ∈ Finset.range 1805, (a i - a (i + 1))) ≤
        ∑ i ∈ Finset.range 1805, P i * (a i - a (i + 1)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi1805 : i < 1805 := Finset.mem_range.mp hi
    have hP1 : 1 ≤ P i := by
      rw [hP]
      exact one_le_naguraWeightPrefix (by omega) (by omega)
    nlinarith [mul_le_mul_of_nonneg_right hP1 (hDiff i)]
  have hExtend :
      (∑ i ∈ Finset.range 1805, P i * (a i - a (i + 1))) ≤
        ∑ i ∈ Finset.range M, P i * (a i - a (i + 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM)
    intro i _ _
    exact mul_nonneg (hP0 i) (hDiff i)
  have hEndpoint : 0 ≤ P M * a M := mul_nonneg (hP0 M) (ha0 M)
  have hAbel := sum_range_mul_eq_partial_sum c a M
  change
    (∑ i ∈ Finset.range (M + 1), naguraWeight (i + 1) * a i) =
      P M * a M +
        ∑ i ∈ Finset.range M, P i * (a i - a (i + 1)) at hAbel
  rw [Finset.sum_range_sub'] at hInitial
  linarith

/-- Zero-based form of Nagura's finite Chebyshev sum. -/
theorem naguraChebyshevSum_eq_sum_range (n : ℕ) :
    naguraChebyshevSum n =
      ∑ i ∈ Finset.range n, Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ) := by
  unfold naguraChebyshevSum
  exact sum_Ioc_zero_eq_sum_range_succ (R := ℝ) _ n

/-- The indicator for multiples of `d` selects exactly the Chebyshev sum at
the divided endpoint. -/
theorem sum_dvd_indicator_psi_eq_chebyshevSum
    (d : ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      if d ∣ i + 1 then Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ) else 0) =
        naguraChebyshevSum (n / d) := by
  rw [naguraChebyshevSum_eq_sum_range]
  calc
    (∑ i ∈ Finset.range n,
        if d ∣ i + 1 then Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ) else 0) =
      ∑ j ∈ Finset.range (n / d),
        Chebyshev.psi ((n / (d * (j + 1)) : ℕ) : ℝ) :=
      sum_dvd_indicator_apply_eq d
        (fun m ↦ Chebyshev.psi ((n / m : ℕ) : ℝ)) n
    _ = ∑ j ∈ Finset.range (n / d),
        Chebyshev.psi (((n / d) / (j + 1) : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.div_div_eq_div_mul]

/-- Exact expansion of Nagura's weighted decreasing sequence as his six-term
Chebyshev combination, before specializing to a multiple of `1806`. -/
theorem sum_naguraWeight_mul_psi_eq (n : ℕ) :
    (∑ i ∈ Finset.range n,
      naguraWeight (i + 1) * Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ)) =
      naguraChebyshevSum n - naguraChebyshevSum (n / 2) -
        naguraChebyshevSum (n / 3) - naguraChebyshevSum (n / 7) -
          naguraChebyshevSum (n / 43) - naguraChebyshevSum (n / 1806) := by
  simp only [naguraWeight, sub_mul, one_mul, Finset.sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← naguraChebyshevSum_eq_sum_range n,
    sum_dvd_indicator_psi_eq_chebyshevSum 2 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 3 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 7 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 43 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 1806 n]







end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraLowerCombination -/
section


/-!
# Nagura's lower Chebyshev combination

The denominators `2, 3, 5, 30` give a second periodic weight whose prefix
sums are always zero or one.  Expanding `ψ` into the von Mangoldt function
therefore shows that the resulting factorial-log combination is at most
`ψ(n)`.
-/

open scoped BigOperators ArithmeticFunction

namespace Erdos390.WholePaper





theorem sum_naguraLowerWeight_eq_prefix (m : ℕ) :
    (∑ i ∈ Finset.range m, naguraLowerWeight (i + 1)) =
      naguraLowerWeightPrefix m := by
  simp only [naguraLowerWeight, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [sum_dvd_indicator_eq_div 2,
    sum_dvd_indicator_eq_div 3,
    sum_dvd_indicator_eq_div 5,
    sum_dvd_indicator_eq_div 30]
  rfl

/-- The lower-combination prefix is exactly a zero-one valued function. -/
theorem naguraLowerWeightPrefix_mem_unitInterval (m : ℕ) :
    0 ≤ naguraLowerWeightPrefix m ∧ naguraLowerWeightPrefix m ≤ 1 := by
  let z : ℤ :=
    (m : ℤ) - ((m / 2 : ℕ) : ℤ) - ((m / 3 : ℕ) : ℤ) -
      ((m / 5 : ℕ) : ℤ) + ((m / 30 : ℕ) : ℤ)
  have hInt : 0 ≤ z ∧ z ≤ 1 := by
    dsimp only [z]
    omega
  have hLower : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hInt.1
  have hUpper : (z : ℝ) ≤ 1 := by exact_mod_cast hInt.2
  dsimp only [z] at hLower hUpper
  push_cast at hLower hUpper
  simpa only [naguraLowerWeightPrefix] using And.intro hLower hUpper



theorem naguraLowerWeightArithmetic_apply {m : ℕ} (hm : m ≠ 0) :
    naguraLowerWeightArithmetic m = naguraLowerWeight m := by
  simp [naguraLowerWeightArithmetic, hm]

/-- Swap the finite `m,q` divisor region after expanding `ψ` into the von
Mangoldt function. -/
theorem sum_lowerWeight_mul_psi_eq_sum_vonMangoldt_mul_prefix (n : ℕ) :
    (∑ m ∈ Finset.Ioc 0 n,
      naguraLowerWeight m * Chebyshev.psi ((n / m : ℕ) : ℝ)) =
      ∑ q ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt q * naguraLowerWeightPrefix (n / q) := by
  let w := naguraLowerWeightArithmetic
  have h₁ := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (R := ℝ) w ArithmeticFunction.vonMangoldt n
  have h₂ := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (R := ℝ) ArithmeticFunction.vonMangoldt w n
  have hConv :
      (∑ r ∈ Finset.Ioc 0 n, (w * ArithmeticFunction.vonMangoldt) r) =
        ∑ r ∈ Finset.Ioc 0 n, (ArithmeticFunction.vonMangoldt * w) r := by
    simp only [mul_comm]
  rw [h₁] at hConv
  rw [h₂] at hConv
  calc
    (∑ m ∈ Finset.Ioc 0 n,
        naguraLowerWeight m * Chebyshev.psi ((n / m : ℕ) : ℝ)) =
      ∑ m ∈ Finset.Ioc 0 n,
        w m *
          (∑ q ∈ Finset.Ioc 0 (n / m),
            ArithmeticFunction.vonMangoldt q) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hm0 : m ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.mp hm).1
      rw [naguraLowerWeightArithmetic_apply hm0]
      simp [Chebyshev.psi]
    _ = ∑ q ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt q *
          (∑ m ∈ Finset.Ioc 0 (n / q), w m) := hConv
    _ = ∑ q ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt q * naguraLowerWeightPrefix (n / q) := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      rw [sum_Ioc_zero_eq_sum_range_succ]
      calc
        (∑ i ∈ Finset.range (n / q), w (i + 1)) =
            ∑ i ∈ Finset.range (n / q), naguraLowerWeight (i + 1) := by
          apply Finset.sum_congr rfl
          intro i _
          exact naguraLowerWeightArithmetic_apply (by omega)
        _ = naguraLowerWeightPrefix (n / q) :=
          sum_naguraLowerWeight_eq_prefix (n / q)



theorem sum_naguraLowerWeight_mul_psi_eq_combination (n : ℕ) :
    (∑ i ∈ Finset.range n,
      naguraLowerWeight (i + 1) *
        Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ)) =
      naguraLowerChebyshevCombination n := by
  simp only [naguraLowerWeight, sub_mul, add_mul, one_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← naguraChebyshevSum_eq_sum_range n,
    sum_dvd_indicator_psi_eq_chebyshevSum 2 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 3 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 5 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 30 n]
  rfl

/-- The combinatorial lower bridge: the `2,3,5,30` factorial combination is
bounded above by `ψ(n)`. -/
theorem naguraLowerChebyshevCombination_le_psi (n : ℕ) :
    naguraLowerChebyshevCombination n ≤ Chebyshev.psi (n : ℝ) := by
  rw [← sum_naguraLowerWeight_mul_psi_eq_combination]
  calc
    (∑ i ∈ Finset.range n,
        naguraLowerWeight (i + 1) *
          Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ)) =
      ∑ m ∈ Finset.Ioc 0 n,
        naguraLowerWeight m * Chebyshev.psi ((n / m : ℕ) : ℝ) := by
      exact (sum_Ioc_zero_eq_sum_range_succ
        (fun m ↦ naguraLowerWeight m *
          Chebyshev.psi ((n / m : ℕ) : ℝ)) n).symm
    _ = ∑ q ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt q * naguraLowerWeightPrefix (n / q) :=
      sum_lowerWeight_mul_psi_eq_sum_vonMangoldt_mul_prefix n
    _ ≤ ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q := by
      apply Finset.sum_le_sum
      intro q _
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := q)
      have hPrefix := (naguraLowerWeightPrefix_mem_unitInterval (n / q)).2
      nlinarith [mul_le_mul_of_nonneg_left hPrefix hΛ]
    _ = Chebyshev.psi (n : ℝ) := by
      simp [Chebyshev.psi]

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraExplicitPsiBounds -/
section


/-!
# Explicit Nagura-style bounds for `ψ` on arithmetic progressions

This file completes the safe factorial/Stirling chain for the lower
`2,3,5,30` combination.  Together with the upper `1806` combination, it gives
fully explicit, unconditional `ψ` estimates at natural endpoints divisible
by the relevant common denominator.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

/-- One-sided lower form of the finite Taylor remainder for `log (1 - x)`. -/
theorem neg_sum_sub_remainder_le_log_one_sub {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) -
        |x| ^ (n + 1) / (1 - |x|) ≤ Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  have hLower := (abs_le.mp h).1
  linarith

theorem log_three_gt_1_098 :
    (549 : ℝ) / 500 < Real.log 3 := by
  have hResidual :
      -(288 : ℝ) / 1000 ≤ Real.log (1 - (1 : ℝ) / 4) := by
    calc
      -(288 : ℝ) / 1000 ≤
          -(∑ i ∈ Finset.range 5,
              ((1 : ℝ) / 4) ^ (i + 1) / (i + 1)) -
            |(1 : ℝ) / 4| ^ (5 + 1) / (1 - |(1 : ℝ) / 4|) := by
        norm_num [Finset.sum_range_succ]
      _ ≤ Real.log (1 - (1 : ℝ) / 4) :=
        neg_sum_sub_remainder_le_log_one_sub (by norm_num) 5
  have hSplit :
      Real.log 3 = 2 * Real.log 2 + Real.log (1 - (1 : ℝ) / 4) := by
    calc
      Real.log 3 = Real.log ((2 : ℝ) ^ 2 * (1 - (1 : ℝ) / 4)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 2) + Real.log (1 - (1 : ℝ) / 4) := by
        rw [Real.log_mul] <;> norm_num
      _ = 2 * Real.log 2 + Real.log (1 - (1 : ℝ) / 4) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_gt_d9]

theorem log_five_gt_1_609 :
    (1609 : ℝ) / 1000 < Real.log 5 := by
  have hResidual :
      -(4703 : ℝ) / 10000 ≤ Real.log (1 - (3 : ℝ) / 8) := by
    calc
      -(4703 : ℝ) / 10000 ≤
          -(∑ i ∈ Finset.range 8,
              ((3 : ℝ) / 8) ^ (i + 1) / (i + 1)) -
            |(3 : ℝ) / 8| ^ (8 + 1) / (1 - |(3 : ℝ) / 8|) := by
        norm_num [Finset.sum_range_succ]
      _ ≤ Real.log (1 - (3 : ℝ) / 8) :=
        neg_sum_sub_remainder_le_log_one_sub (by norm_num) 8
  have hSplit :
      Real.log 5 = 3 * Real.log 2 + Real.log (1 - (3 : ℝ) / 8) := by
    calc
      Real.log 5 = Real.log ((2 : ℝ) ^ 3 * (1 - (3 : ℝ) / 8)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 3) + Real.log (1 - (3 : ℝ) / 8) := by
        rw [Real.log_mul] <;> norm_num
      _ = 3 * Real.log 2 + Real.log (1 - (3 : ℝ) / 8) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_gt_d9]

theorem log_thirty_lt_3_402 :
    Real.log 30 < (1701 : ℝ) / 500 := by
  have hResidual :
      Real.log (1 - (1 : ℝ) / 16) ≤ -(641 : ℝ) / 10000 := by
    calc
      Real.log (1 - (1 : ℝ) / 16) ≤
          -(∑ i ∈ Finset.range 2,
              ((1 : ℝ) / 16) ^ (i + 1) / (i + 1)) +
            |(1 : ℝ) / 16| ^ (2 + 1) / (1 - |(1 : ℝ) / 16|) :=
        log_one_sub_le_neg_sum_add_remainder (by norm_num) 2
      _ ≤ -(641 : ℝ) / 10000 := by
        norm_num [Finset.sum_range_succ]
  have hSplit :
      Real.log 30 = 5 * Real.log 2 + Real.log (1 - (1 : ℝ) / 16) := by
    calc
      Real.log 30 = Real.log ((2 : ℝ) ^ 5 * (1 - (1 : ℝ) / 16)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 5) + Real.log (1 - (1 : ℝ) / 16) := by
        rw [Real.log_mul] <;> norm_num
      _ = 5 * Real.log 2 + Real.log (1 - (1 : ℝ) / 16) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_lt_d9]



theorem naguraLowerMainCoefficient_gt_0_9209 :
    (9209 : ℝ) / 10000 < naguraLowerMainCoefficient := by
  unfold naguraLowerMainCoefficient
  nlinarith [Real.log_two_gt_d9, log_three_gt_1_098,
    log_five_gt_1_609, log_thirty_lt_3_402]





















end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraGeneralUpperModel -/
section


/-!
# A floor-uniform upper model for Nagura's first combination

This is the general-integer counterpart of the exact `1806 k` calculation.
For each denominator, `floor (n / d)` is replaced by a real lower endpoint;
all rounding losses remain explicit.
-/

namespace Erdos390.WholePaper





/-- The real lower model lies below the proved Stirling model at the natural
floor. -/
theorem naguraFloorFactorialLowerModel_le
    {n d : ℕ} (hd : 0 < d) (hnd : 2 * d ≤ n + 1) :
    naguraFloorFactorialLowerModel n d ≤
      naguraFactorialLogLower (n / d) := by
  let x : ℝ := n
  let q : ℝ := (n / d : ℕ)
  let y : ℝ := (x - d + 1) / d
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hMulLe : n / d * d ≤ n := Nat.div_mul_le_self n d
  have hLt : n < d * (n / d + 1) := Nat.lt_mul_div_succ n hd
  have hLowerNat : n + 1 ≤ d * (n / d + 1) := by omega
  have hMulLeR : q * (d : ℝ) ≤ x := by
    dsimp only [q, x]
    exact_mod_cast hMulLe
  have hLowerR : (n : ℝ) + 1 ≤ (d : ℝ) * ((n / d : ℕ) + 1) := by
    exact_mod_cast hLowerNat
  have hqy : y ≤ q := by
    dsimp only [y, q, x]
    apply (div_le_iff₀ hdR).2
    nlinarith
  have hqUpper : q ≤ x / d := by
    apply (le_div_iff₀ hdR).2
    exact hMulLeR
  have hyOne : 1 ≤ y := by
    have hndR : 2 * (d : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hnd
    dsimp only [y, x]
    apply (le_div_iff₀ hdR).2
    nlinarith
  have hyPos : 0 < y := zero_lt_one.trans_le hyOne
  have hLog : Real.log y ≤ Real.log q :=
    Real.log_le_log hyPos hqy
  have hLogNonneg : 0 ≤ Real.log y := Real.log_nonneg hyOne
  have hqNonneg : 0 ≤ q := by positivity
  have hMulLog : y * Real.log y ≤ q * Real.log q :=
    mul_le_mul hqy hLog hLogNonneg hqNonneg
  simp only [naguraFloorFactorialLowerModel, naguraFactorialLogLower]
  change
    y * Real.log y - x / d + Real.log y / 2 +
        Real.log (2 * Real.pi) / 2 ≤
      q * Real.log q - q + Real.log q / 2 +
        Real.log (2 * Real.pi) / 2
  linarith



theorem naguraGeneralUpperCombination_le_model
    {n : ℕ} (hn : 20000 ≤ n) :
    naguraGeneralUpperCombination n ≤ naguraGeneralUpperModel n := by
  have hn0 : n ≠ 0 := by omega
  have h2 : n / 2 ≠ 0 := by omega
  have h3 : n / 3 ≠ 0 := by omega
  have h7 : n / 7 ≠ 0 := by omega
  have h43 : n / 43 ≠ 0 := by omega
  have h1806 : n / 1806 ≠ 0 := by omega
  have hUpper := log_factorial_le_naguraFactorialLogUpper hn0
  have h2Stirling := naguraFactorialLogLower_le_log_factorial h2
  have h3Stirling := naguraFactorialLogLower_le_log_factorial h3
  have h7Stirling := naguraFactorialLogLower_le_log_factorial h7
  have h43Stirling := naguraFactorialLogLower_le_log_factorial h43
  have h1806Stirling := naguraFactorialLogLower_le_log_factorial h1806
  have h2Floor := naguraFloorFactorialLowerModel_le
    (n := n) (d := 2) (by norm_num) (by omega)
  have h3Floor := naguraFloorFactorialLowerModel_le
    (n := n) (d := 3) (by norm_num) (by omega)
  have h7Floor := naguraFloorFactorialLowerModel_le
    (n := n) (d := 7) (by norm_num) (by omega)
  have h43Floor := naguraFloorFactorialLowerModel_le
    (n := n) (d := 43) (by norm_num) (by omega)
  have h1806Floor := naguraFloorFactorialLowerModel_le
    (n := n) (d := 1806) (by norm_num) (by omega)
  simp only [naguraGeneralUpperCombination, naguraChebyshevSum_eq_log_factorial]
  unfold naguraGeneralUpperModel
  linarith

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraGeneralUpperBound -/
section


/-!
# The general-integer upper estimate in Nagura's Lemma 2

All floor losses from the first combination are bounded uniformly.  The
threshold `20000` is intentionally conservative; the already-certified prime
chain covers the lower finite range needed by the final application.
-/

namespace Erdos390.WholePaper

/-- Elementary lower bound for the logarithm of Nagura's shifted quotient. -/
theorem log_shifted_div_lower {x d : ℝ} (hd : 1 ≤ d) (hxd : d < x) :
    Real.log ((x - d + 1) / d) ≥
      Real.log x - Real.log d - (d - 1) / (x - d + 1) := by
  have hdPos : 0 < d := zero_lt_one.trans_le hd
  have hxPos : 0 < x := hdPos.trans hxd
  have hDenomPos : 0 < x - d + 1 := by linarith
  let z : ℝ := (x - d + 1) / x
  have hz : 0 < z := by
    dsimp only [z]
    positivity
  have hResidual := Real.one_sub_inv_le_log_of_pos hz
  have hResidual' :
      -(d - 1) / (x - d + 1) ≤ Real.log z := by
    calc
      -(d - 1) / (x - d + 1) = 1 - z⁻¹ := by
        dsimp only [z]
        field_simp
        ring
      _ ≤ Real.log z := hResidual
  have hFactor : (x - d + 1) / d = (x / d) * z := by
    dsimp only [z]
    field_simp
  have hSplit :
      Real.log ((x - d + 1) / d) =
        Real.log x - Real.log d + Real.log z := by
    rw [hFactor, Real.log_mul (div_ne_zero (ne_of_gt hxPos) (ne_of_gt hdPos))
      (ne_of_gt hz), Real.log_div (ne_of_gt hxPos) (ne_of_gt hdPos)]
  rw [hSplit]
  calc
    Real.log x - Real.log d - (d - 1) / (x - d + 1) =
        (Real.log x - Real.log d) + (-(d - 1) / (x - d + 1)) := by ring
    _ ≤ (Real.log x - Real.log d) + Real.log z :=
      by linarith
    _ = Real.log x - Real.log d + Real.log z := by ring



theorem naguraFloorFactorialCoarseModel_le
    {n d : ℕ} (hd : 0 < d) (hnd : 2 * d ≤ n) :
    naguraFloorFactorialCoarseModel n d ≤
      naguraFloorFactorialLowerModel n d := by
  let x : ℝ := n
  let δ : ℝ := d
  let y : ℝ := (x - δ + 1) / δ
  let L : ℝ := Real.log x - Real.log δ - (δ - 1) / (x - δ + 1)
  have hdR : 1 ≤ δ := by
    dsimp only [δ]
    exact_mod_cast hd
  have hxd : δ < x := by
    dsimp only [δ, x]
    exact_mod_cast (by omega : d < n)
  have hLog : L ≤ Real.log y := by
    exact log_shifted_div_lower hdR hxd
  have hyOne : 1 ≤ y := by
    have hdPos : 0 < δ := zero_lt_one.trans_le hdR
    have hndR : 2 * δ ≤ x := by
      dsimp only [δ, x]
      exact_mod_cast hnd
    dsimp only [y]
    apply (le_div_iff₀ hdPos).2
    linarith
  have hCoeff : 0 ≤ y + 1 / 2 := by linarith
  have hMul := mul_le_mul_of_nonneg_left hLog hCoeff
  simp only [naguraFloorFactorialCoarseModel,
    naguraFloorFactorialLowerModel]
  change
    y * L - x / δ + L / 2 + Real.log (2 * Real.pi) / 2 ≤
      y * Real.log y - x / δ + Real.log y / 2 +
        Real.log (2 * Real.pi) / 2
  nlinarith



theorem naguraGeneralUpperModel_le_coarse
    {n : ℕ} (hn : 20000 ≤ n) :
    naguraGeneralUpperModel n ≤ naguraGeneralUpperCoarseModel n := by
  have h2 := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 2) (by norm_num) (by omega)
  have h3 := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 3) (by norm_num) (by omega)
  have h7 := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 7) (by norm_num) (by omega)
  have h43 := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 43) (by norm_num) (by omega)
  have h1806 := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 1806) (by norm_num) (by omega)
  unfold naguraGeneralUpperModel naguraGeneralUpperCoarseModel
  linarith



/-- A small algebra lemma, kept separate so clearing a shifted denominator
never creates the enormous common-denominator expression for all five
floors at once. -/
theorem nagura_floor_coarse_algebra
    {x δ A P : ℝ} (hδ : δ ≠ 0) (hshift : x - δ + 1 ≠ 0) :
    ((x - δ + 1) / δ) * (A - (δ - 1) / (x - δ + 1)) - x / δ +
        (A - (δ - 1) / (x - δ + 1)) / 2 + P / 2 =
      x / δ * A - (δ - 1) / δ * A - (δ - 1) / δ - x / δ +
        A / 2 - ((δ - 1) / (x - δ + 1)) / 2 + P / 2 := by
  field_simp [hδ, hshift]
  ring

/-- Exact algebraic expansion of the coarse model. -/
theorem naguraGeneralUpperCoarseModel_eq {n : ℕ} (hn : 20000 ≤ n) :
    naguraGeneralUpperCoarseModel n =
      (n : ℝ) * naguraMainCoefficient + (5 : ℝ) / 2 * Real.log (n : ℝ) +
        naguraMainCoefficient -
          (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
            Real.log 1806) / 2 +
        5 - 5 * Real.log (2 * Real.pi) / 2 +
          naguraUpperRoundingError n := by
  simp only [naguraGeneralUpperCoarseModel, naguraFactorialLogUpper,
    naguraFloorFactorialCoarseModel, naguraMainCoefficient,
    naguraUpperRoundingError, Nat.cast_ofNat]
  have hnR : (20000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (n : ℝ) - 2 + 1 ≠ 0 := by nlinarith
  have h2 : (n : ℝ) - 3 + 1 ≠ 0 := by nlinarith
  have h6 : (n : ℝ) - 7 + 1 ≠ 0 := by nlinarith
  have h42 : (n : ℝ) - 43 + 1 ≠ 0 := by nlinarith
  have h1805 : (n : ℝ) - 1806 + 1 ≠ 0 := by nlinarith
  rw [nagura_floor_coarse_algebra (by norm_num) h1,
    nagura_floor_coarse_algebra (by norm_num) h2,
    nagura_floor_coarse_algebra (by norm_num) h6,
    nagura_floor_coarse_algebra (by norm_num) h42,
    nagura_floor_coarse_algebra (by norm_num) h1805]
  ring

theorem naguraUpperRoundingError_le_two_point_five
    {x : ℝ} (hx : 20000 ≤ x) :
    naguraUpperRoundingError x ≤ (5 : ℝ) / 2 := by
  have h1 : 1 / (x - 1) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have h2 : 2 / (x - 2) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have h6 : 6 / (x - 6) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have h42 : 42 / (x - 42) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have h1805 : 1805 / (x - 1805) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  unfold naguraUpperRoundingError
  linarith

theorem log_nat_lt_div_ten_thousand_add_nine
    {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) < (n : ℝ) / 10000 + 9 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hSmall := Real.log_le_sub_one_of_pos
    (show 0 < (n : ℝ) / 10000 by positivity)
  have hLogTenThousand : Real.log 10000 < 10 := by
    have hMono : Real.log (10000 : ℝ) < Real.log ((2 : ℝ) ^ 14) :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    rw [Real.log_pow] at hMono
    norm_num at hMono
    nlinarith [Real.log_two_lt_d9]
  have hSplit :
      Real.log (n : ℝ) =
        Real.log ((n : ℝ) / 10000) + Real.log 10000 := by
    calc
      Real.log (n : ℝ) = Real.log (((n : ℝ) / 10000) * 10000) := by
        congr 1
        field_simp
      _ = Real.log ((n : ℝ) / 10000) + Real.log 10000 :=
        Real.log_mul (div_ne_zero hnR (by norm_num)) (by norm_num)
  rw [hSplit]
  linarith

/-- One extra Taylor term at `7 / 8` gives enough coefficient room to
absorb the recursive `ψ(n / 1806)` term in the far tail. -/
theorem log_seven_lt_1_9465 :
    Real.log 7 < (3893 : ℝ) / 2000 := by
  have hResidual :
      Real.log (1 - (1 : ℝ) / 8) ≤ -(1331 : ℝ) / 10000 := by
    calc
      Real.log (1 - (1 : ℝ) / 8) ≤
          -(∑ i ∈ Finset.range 3,
              ((1 : ℝ) / 8) ^ (i + 1) / (i + 1)) +
            |(1 : ℝ) / 8| ^ (3 + 1) / (1 - |(1 : ℝ) / 8|) :=
        log_one_sub_le_neg_sum_add_remainder (by norm_num) 3
      _ ≤ -(1331 : ℝ) / 10000 := by
        norm_num [Finset.sum_range_succ]
  have hSplit :
      Real.log 7 = 3 * Real.log 2 + Real.log (1 - (1 : ℝ) / 8) := by
    calc
      Real.log 7 = Real.log ((2 : ℝ) ^ 3 * (1 - (1 : ℝ) / 8)) := by
        norm_num
      _ = Real.log ((2 : ℝ) ^ 3) + Real.log (1 - (1 : ℝ) / 8) := by
        rw [Real.log_mul] <;> norm_num
      _ = 3 * Real.log 2 + Real.log (1 - (1 : ℝ) / 8) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_lt_d9]

theorem naguraMainCoefficient_lt_1_0827 :
    naguraMainCoefficient < (10827 : ℝ) / 10000 := by
  unfold naguraMainCoefficient
  nlinarith [Real.log_two_lt_d9, log_three_lt_1_099,
    log_seven_lt_1_9465, log_forty_three_lt_3_762,
    log_one_thousand_eight_hundred_six_lt_seven_point_five]



/-- A sharper far-tail version of the first combination estimate. -/
theorem naguraGeneralUpperCombination_lt_1_083_mul
    {n : ℕ} (hn : 1000000 ≤ n) :
    naguraGeneralUpperCombination n <
      (1083 : ℝ) / 1000 * (n : ℝ) := by
  have hnSmall : 20000 ≤ n := by omega
  have hModel := naguraGeneralUpperCombination_le_model hnSmall
  have hCoarse := naguraGeneralUpperModel_le_coarse hnSmall
  have hIdentity := naguraGeneralUpperCoarseModel_eq hnSmall
  have hnPos : 0 < n := by omega
  have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hCoefficient := naguraMainCoefficient_lt_1_0827
  have hMain := mul_lt_mul_of_pos_left hCoefficient
    (show 0 < (n : ℝ) by exact_mod_cast hnPos)
  have hLog := log_nat_lt_div_ten_thousand_add_nine hnPos
  have hError := naguraUpperRoundingError_le_two_point_five
    (show (20000 : ℝ) ≤ (n : ℝ) by exact_mod_cast hnSmall)
  have hLogSum :
      0 ≤ Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
        Real.log 1806 := by
    positivity
  have hPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  rw [hIdentity] at hCoarse
  nlinarith

/-- General-endpoint combinatorial bridge for the first Nagura weight. -/
theorem psi_sub_psi_div_1806_le_generalUpperCombination
    {n : ℕ} (hn : 1806 ≤ n) :
    Chebyshev.psi (n : ℝ) - Chebyshev.psi ((n / 1806 : ℕ) : ℝ) ≤
      naguraGeneralUpperCombination n := by
  let a : ℕ → ℝ := fun i ↦
    Chebyshev.psi (((n / (i + 1) : ℕ) : ℝ))
  have ha : Antitone a := by
    intro i j hij
    apply Chebyshev.psi_mono
    norm_cast
    apply (Nat.le_div_iff_mul_le (by omega : 0 < i + 1)).2
    calc
      (n / (j + 1)) * (i + 1) ≤ (n / (j + 1)) * (j + 1) := by
        exact Nat.mul_le_mul_left _ (Nat.succ_le_succ hij)
      _ ≤ n := Nat.div_mul_le_self _ _
  have ha0 (i : ℕ) : 0 ≤ a i := Chebyshev.psi_nonneg _
  have h := first_sub_1806_le_nagura_weighted_sum a ha ha0 hn
  dsimp only [a] at h
  rw [sum_naguraWeight_mul_psi_eq] at h
  simpa only [Nat.zero_add, Nat.div_one, Nat.reduceAdd,
    naguraGeneralUpperCombination] using h

/-- The sharp upper bound for `ψ` at every natural endpoint in the analytic
tail. -/
theorem psi_nat_lt_1_086_mul {n : ℕ} (hn : 1000000 ≤ n) :
    Chebyshev.psi (n : ℝ) < (543 : ℝ) / 500 * (n : ℝ) := by
  have hnBridge : 1806 ≤ n := by omega
  have hBridge := psi_sub_psi_div_1806_le_generalUpperCombination hnBridge
  have hCombination := naguraGeneralUpperCombination_lt_1_083_mul hn
  have hqPosNat : 0 < n / 1806 := Nat.div_pos (by omega) (by norm_num)
  have hqPos : 0 < ((n / 1806 : ℕ) : ℝ) := by exact_mod_cast hqPosNat
  have hPsi := Chebyshev.psi_le_const_mul_self
    (x := ((n / 1806 : ℕ) : ℝ)) hqPos.le
  have hLogFour : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hCoarseConstant : Real.log 4 + 4 < (2709 : ℝ) / 500 := by
    rw [hLogFour]
    nlinarith [Real.log_two_lt_d9]
  have hCoarseTerm := mul_lt_mul_of_pos_right hCoarseConstant hqPos
  have hMulLe : (n / 1806) * 1806 ≤ n := Nat.div_mul_le_self n 1806
  have hMulLeR : ((n / 1806 : ℕ) : ℝ) * 1806 ≤ (n : ℝ) := by
    exact_mod_cast hMulLe
  nlinarith

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraGeneralLowerBound -/
section


/-!
# The general-integer lower estimate in Nagura's Lemma 2

The three negatively signed factorials are evaluated at floors.  Bounding
each floor between `x / d - 1` and `x / d` costs only one additive unit in
the elementary factorial majorant.  The positively signed `n / 30` term
uses the same shifted Stirling minorant as the general upper estimate.
-/

namespace Erdos390.WholePaper



theorem naguraFactorialLogUpper_div_le_coarse
    {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    naguraFactorialLogUpper (n / d) ≤
      naguraFactorialUpperDivCoarseModel n d := by
  let x : ℝ := n
  let δ : ℝ := d
  let q : ℝ := (n / d : ℕ)
  let t : ℝ := x / δ
  have hdR : 0 < δ := by
    dsimp only [δ]
    exact_mod_cast hd
  have hxR : 0 < x := by
    dsimp only [x]
    exact_mod_cast (lt_of_lt_of_le hd hdn)
  have hqPosNat : 0 < n / d := Nat.div_pos hdn hd
  have hqPos : 0 < q := by
    dsimp only [q]
    exact_mod_cast hqPosNat
  have hqOneNat : 1 ≤ n / d := by omega
  have hqOne : 1 ≤ q := by
    dsimp only [q]
    exact_mod_cast hqOneNat
  have hMulLe : n / d * d ≤ n := Nat.div_mul_le_self n d
  have hMulLeR : q * δ ≤ x := by
    dsimp only [q, δ, x]
    exact_mod_cast hMulLe
  have hqt : q ≤ t := by
    dsimp only [t]
    exact (le_div_iff₀ hdR).2 hMulLeR
  have hLt : n < d * (n / d + 1) := Nat.lt_mul_div_succ n hd
  have hLtR : x < δ * (q + 1) := by
    dsimp only [x, δ, q]
    exact_mod_cast hLt
  have htq : t < q + 1 := by
    dsimp only [t]
    exact (div_lt_iff₀ hdR).2 (by nlinarith)
  have htOne : 1 ≤ t := hqOne.trans hqt
  have htPos : 0 < t := zero_lt_one.trans_le htOne
  have hLog : Real.log q ≤ Real.log t := Real.log_le_log hqPos hqt
  have hLogQNonneg : 0 ≤ Real.log q := Real.log_nonneg hqOne
  have hMulLog : q * Real.log q ≤ t * Real.log t :=
    mul_le_mul hqt hLog hLogQNonneg htPos.le
  have hLogSplit : Real.log t = Real.log x - Real.log δ := by
    dsimp only [t]
    exact Real.log_div (ne_of_gt hxR) (ne_of_gt hdR)
  simp only [naguraFactorialLogUpper,
    naguraFactorialUpperDivCoarseModel]
  change
    q * Real.log q - q + Real.log q + 1 ≤
      t * (Real.log x - Real.log δ) - t +
        (Real.log x - Real.log δ) + 2
  rw [← hLogSplit]
  linarith



theorem naguraGeneralLowerModel_le_combination
    {n : ℕ} (hn : 20000 ≤ n) :
    naguraGeneralLowerModel n ≤ naguraLowerChebyshevCombination n := by
  have hn0 : n ≠ 0 := by omega
  have h30 : n / 30 ≠ 0 := by omega
  have hLower := naguraFactorialLogLower_le_log_factorial hn0
  have h2Upper := log_factorial_le_naguraFactorialLogUpper
    (show n / 2 ≠ 0 by omega)
  have h3Upper := log_factorial_le_naguraFactorialLogUpper
    (show n / 3 ≠ 0 by omega)
  have h5Upper := log_factorial_le_naguraFactorialLogUpper
    (show n / 5 ≠ 0 by omega)
  have h30Lower := naguraFactorialLogLower_le_log_factorial h30
  have h2Coarse := naguraFactorialLogUpper_div_le_coarse
    (n := n) (d := 2) (by norm_num) (by omega)
  have h3Coarse := naguraFactorialLogUpper_div_le_coarse
    (n := n) (d := 3) (by norm_num) (by omega)
  have h5Coarse := naguraFactorialLogUpper_div_le_coarse
    (n := n) (d := 5) (by norm_num) (by omega)
  have h30Floor := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 30) (by norm_num) (by omega)
  have h30Model := naguraFloorFactorialLowerModel_le
    (n := n) (d := 30) (by norm_num) (by omega)
  simp only [naguraLowerChebyshevCombination,
    naguraChebyshevSum_eq_log_factorial]
  unfold naguraGeneralLowerModel
  linarith



/-- Exact expansion of the lower coarse model. -/
theorem naguraGeneralLowerModel_eq {n : ℕ} (hn : 20000 ≤ n) :
    naguraGeneralLowerModel n =
      (n : ℝ) * naguraLowerMainCoefficient -
        (89 : ℝ) / 30 * Real.log (n : ℝ) +
        Real.log 2 + Real.log 3 + Real.log 5 +
        (7 : ℝ) / 15 * Real.log 30 + Real.log (2 * Real.pi) -
        (209 : ℝ) / 30 - naguraLowerRoundingError n := by
  simp only [naguraGeneralLowerModel, naguraFactorialLogLower,
    naguraFactorialUpperDivCoarseModel,
    naguraFloorFactorialCoarseModel, naguraLowerMainCoefficient,
    naguraLowerRoundingError, Nat.cast_ofNat]
  have hnR : (20000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h29 : (n : ℝ) - 30 + 1 ≠ 0 := by nlinarith
  rw [nagura_floor_coarse_algebra (by norm_num) h29]
  ring

theorem naguraLowerRoundingError_le_half
    {x : ℝ} (hx : 20000 ≤ x) :
    naguraLowerRoundingError x ≤ (1 : ℝ) / 2 := by
  have h : 29 / (x - 30 + 1) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  unfold naguraLowerRoundingError
  linarith

/-- The general-integer form of Nagura's second analytic estimate. -/
theorem naguraGeneralLowerCombination_gt_0_916_mul
    {n : ℕ} (hn : 20000 ≤ n) :
    (229 : ℝ) / 250 * (n : ℝ) <
      naguraLowerChebyshevCombination n := by
  have hModel := naguraGeneralLowerModel_le_combination hn
  have hIdentity := naguraGeneralLowerModel_eq hn
  have hnPos : 0 < n := by omega
  have hnR : (20000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hCoefficient := naguraLowerMainCoefficient_gt_0_9209
  have hMain := mul_lt_mul_of_pos_left hCoefficient
    (show 0 < (n : ℝ) by exact_mod_cast hnPos)
  have hLog := log_nat_lt_div_ten_thousand_add_nine hnPos
  have hError := naguraLowerRoundingError_le_half hnR
  have hPositiveLogs :
      0 ≤ Real.log 2 + Real.log 3 + Real.log 5 +
        (7 : ℝ) / 15 * Real.log 30 + Real.log (2 * Real.pi) := by
    have hPi : 0 ≤ Real.log (2 * Real.pi) := by
      apply Real.log_nonneg
      nlinarith [Real.pi_gt_three]
    positivity
  rw [hIdentity] at hModel
  nlinarith

/-- Consequently `ψ(n) > 0.916 n` throughout the analytic tail. -/
theorem psi_nat_gt_0_916_mul {n : ℕ} (hn : 20000 ≤ n) :
    (229 : ℝ) / 250 * (n : ℝ) < Chebyshev.psi (n : ℝ) := by
  exact (naguraGeneralLowerCombination_gt_0_916_mul hn).trans_le
    (naguraLowerChebyshevCombination_le_psi n)

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraPsiBridge -/
section


/-!
# The Chebyshev-function bridge in Nagura's argument

This file isolates the assumption-free combinatorial part of Nagura's
explicit proof.  Strict growth of `Chebyshev.theta` across a natural interval
forces a prime in that interval.  Mathlib's proved comparison between
`Chebyshev.psi` and `Chebyshev.theta` then turns a concrete `psi` gap into the
strict natural-number Nagura conclusion.

No explicit estimate for `psi` is assumed globally here.  Proving the concrete
gap in `hasNaguraPrime_of_psi_gap` uniformly is precisely the remaining
effective analytic step.
-/

namespace Erdos390.WholePaper



theorem naguraStrictUpper_spec {n : ℕ} (hn : 25 ≤ n) :
    n < naguraStrictUpper n ∧ 5 * naguraStrictUpper n < 6 * n := by
  constructor
  · have hdiv : n + 1 ≤ (6 * n - 1) / 5 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 5)]
      omega
    simpa only [naguraStrictUpper, Nat.lt_iff_add_one_le] using hdiv
  · have hmul : 5 * ((6 * n - 1) / 5) ≤ 6 * n - 1 := by
      rw [mul_comm]
      exact Nat.div_mul_le_self (6 * n - 1) 5
    simpa only [naguraStrictUpper] using hmul.trans_lt (by omega)

/-- A strict increase of `theta` between natural endpoints detects an actual
prime in the corresponding half-open interval. -/
theorem exists_prime_Ioc_of_theta_lt {a b : ℕ}
    (hTheta : Chebyshev.theta (a : ℝ) < Chebyshev.theta (b : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b := by
  have hab : a ≤ b := by
    by_contra hba
    have hba' : b ≤ a := Nat.le_of_not_ge hba
    have hmono :
        Chebyshev.theta (b : ℝ) ≤ Chebyshev.theta (a : ℝ) :=
      Chebyshev.theta_mono (by exact_mod_cast hba')
    exact (not_lt_of_ge hmono) hTheta
  by_contra hNoPrime
  have hNoPrime' :
      ∀ p : ℕ, p.Prime → a < p → p ≤ b → False := by
    intro p hpPrime hap hpb
    exact hNoPrime ⟨p, hpPrime, hap, hpb⟩
  have hFinset :
      (Finset.Icc 0 a).filter Nat.Prime =
        (Finset.Icc 0 b).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hpZero, hpa⟩, hpPrime⟩
      exact ⟨⟨hpZero, hpa.trans hab⟩, hpPrime⟩
    · rintro ⟨⟨hpZero, hpb⟩, hpPrime⟩
      have hpa : p ≤ a := by
        by_contra hap
        exact hNoPrime' p hpPrime (Nat.lt_of_not_ge hap) hpb
      exact ⟨⟨hpZero, hpa⟩, hpPrime⟩
  have hThetaEq :
      Chebyshev.theta (a : ℝ) = Chebyshev.theta (b : ℝ) := by
    rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
    simpa only [Nat.floor_natCast] using congrArg
      (fun s : Finset ℕ => ∑ p ∈ s, Real.log p) hFinset
  exact (ne_of_lt hTheta) hThetaEq

/-- A concrete Chebyshev `psi` gap implies the strict natural-number Nagura
conclusion.  The error term is the already-proved Mathlib comparison
`|psi y - theta y| ≤ 2 sqrt(y) log(y)`. -/
theorem hasNaguraPrime_of_psi_gap {n : ℕ} (hn : 25 ≤ n)
    (hPsiGap :
      Chebyshev.psi (n : ℝ) +
          2 * Real.sqrt (naguraStrictUpper n : ℝ) *
            Real.log (naguraStrictUpper n : ℝ) <
        Chebyshev.psi (naguraStrictUpper n : ℝ)) :
    HasNaguraPrime n := by
  have hUpperSpec := naguraStrictUpper_spec hn
  have hUpperOne : (1 : ℝ) ≤ naguraStrictUpper n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hPsiTheta :=
    Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hUpperOne
  have hErrorUpper :
      Chebyshev.psi (naguraStrictUpper n : ℝ) -
          Chebyshev.theta (naguraStrictUpper n : ℝ) ≤
        2 * Real.sqrt (naguraStrictUpper n : ℝ) *
          Real.log (naguraStrictUpper n : ℝ) :=
    (le_abs_self _).trans hPsiTheta
  have hThetaPsi :
      Chebyshev.theta (n : ℝ) ≤ Chebyshev.psi (n : ℝ) :=
    Chebyshev.theta_le_psi (n : ℝ)
  have hThetaGap :
      Chebyshev.theta (n : ℝ) <
        Chebyshev.theta (naguraStrictUpper n : ℝ) := by
    linarith
  obtain ⟨p, hpPrime, hnp, hpUpper⟩ :=
    exists_prime_Ioc_of_theta_lt hThetaGap
  refine ⟨p, hpPrime, hnp, ?_⟩
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 5 hpUpper) hUpperSpec.2

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraAnalyticTail -/
section


/-!
# An explicit analytic tail for Nagura's interval

The arbitrary-endpoint bounds for `ψ` leave a linear gap of size about
`0.0132 n`.  A scaled elementary logarithm estimate makes Mathlib's
`2 sqrt(x) log(x)` comparison error smaller than `x / 100` once
`x ≥ 16,000,000`.
-/

namespace Erdos390.WholePaper

/-- Beyond sixteen million, the square-root error dominates the logarithm
by the explicit factor needed below. -/
theorem log_lt_sqrt_div_two_hundred {x : ℝ} (hx : 16000000 ≤ x) :
    Real.log x < Real.sqrt x / 200 := by
  have hxPos : 0 < x := by linarith
  let t : ℝ := Real.sqrt x
  have htNonneg : 0 ≤ t := by
    dsimp only [t]
    positivity
  have htSq : t ^ 2 = x := by
    dsimp only [t]
    exact Real.sq_sqrt hxPos.le
  have htLower : 4000 ≤ t := by nlinarith
  have htPos : 0 < t := by linarith
  have hSmall := Real.log_le_sub_one_of_pos
    (show 0 < t / 1000 by positivity)
  have hLogThousand : Real.log 1000 < 7 := by
    have hMono : Real.log (1000 : ℝ) < Real.log ((2 : ℝ) ^ 10) :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    rw [Real.log_pow] at hMono
    norm_num at hMono
    linarith [Real.log_two_lt_d9]
  have hSplit :
      Real.log t = Real.log (t / 1000) + Real.log 1000 := by
    calc
      Real.log t = Real.log ((t / 1000) * 1000) := by
        congr 1
        field_simp
      _ = Real.log (t / 1000) + Real.log 1000 :=
        Real.log_mul (div_ne_zero (ne_of_gt htPos) (by norm_num))
          (by norm_num)
  have hLogT : Real.log t < t / 400 := by
    rw [hSplit]
    linarith
  have hLogX : Real.log x = 2 * Real.log t := by
    calc
      Real.log x = Real.log (t ^ 2) := by rw [htSq]
      _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
  rw [hLogX]
  linarith

theorem two_sqrt_mul_log_lt_div_one_hundred {x : ℝ}
    (hx : 16000000 ≤ x) :
    2 * Real.sqrt x * Real.log x < x / 100 := by
  have hxPos : 0 < x := by linarith
  have hLog := log_lt_sqrt_div_two_hundred hx
  have hSqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxPos
  have hMul := mul_lt_mul_of_pos_left hLog
    (show 0 < 2 * Real.sqrt x by positivity)
  have hSq := Real.sq_sqrt hxPos.le
  calc
    2 * Real.sqrt x * Real.log x <
        2 * Real.sqrt x * (Real.sqrt x / 200) := by
      simpa only [mul_assoc] using hMul
    _ = (Real.sqrt x) ^ 2 / 100 := by ring
    _ = x / 100 := by rw [hSq]

/-- The fully explicit analytic tail of Nagura's theorem. -/
theorem exists_prime_nagura_analytic_tail {n : ℕ}
    (hn : 16000000 ≤ n) : HasNaguraPrime n := by
  let u := naguraStrictUpper n
  have hnUpper : 1000000 ≤ n := by omega
  have huThreshold : 16000000 ≤ u := by
    dsimp only [u, naguraStrictUpper]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 5)]
    omega
  have huLower : 20000 ≤ u := by omega
  have hPsiUpper := psi_nat_lt_1_086_mul hnUpper
  have hPsiLower := psi_nat_gt_0_916_mul huLower
  have hError := two_sqrt_mul_log_lt_div_one_hundred
    (show (16000000 : ℝ) ≤ (u : ℝ) by exact_mod_cast huThreshold)
  have hFloorLower : 6 * n ≤ 5 * u + 5 := by
    dsimp only [u, naguraStrictUpper]
    have hDiv := Nat.lt_mul_div_succ (6 * n - 1)
      (by norm_num : 0 < 5)
    omega
  have hFloorLowerR :
      (6 : ℝ) * (n : ℝ) ≤ 5 * (u : ℝ) + 5 := by
    exact_mod_cast hFloorLower
  have hnR : (16000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNumeric :
      (543 : ℝ) / 500 * (n : ℝ) + (u : ℝ) / 100 <
        (229 : ℝ) / 250 * (u : ℝ) := by
    linarith
  have hGap :
      Chebyshev.psi (n : ℝ) +
          2 * Real.sqrt (u : ℝ) * Real.log (u : ℝ) <
        Chebyshev.psi (u : ℝ) := by
    calc
      Chebyshev.psi (n : ℝ) +
            2 * Real.sqrt (u : ℝ) * Real.log (u : ℝ) <
          (543 : ℝ) / 500 * (n : ℝ) + (u : ℝ) / 100 :=
        add_lt_add hPsiUpper hError
      _ < (229 : ℝ) / 250 * (u : ℝ) := hNumeric
      _ < Chebyshev.psi (u : ℝ) := hPsiLower
  exact hasNaguraPrime_of_psi_gap (by omega) hGap

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraPrimeChain91639To218737 -/
section


namespace Erdos390.WholePaper

theorem exists_prime_nagura_91639_to_218737 {n : ℕ}
    (hnLower : 91639 ≤ n) (hnUpper : n < 218737) : HasNaguraPrime n := by
  by_cases h109063 : n < 109063
  · exact ⟨109063, by norm_num, h109063, by omega⟩
  by_cases h129793 : n < 129793
  · exact ⟨129793, by norm_num, h129793, by omega⟩
  by_cases h154459 : n < 154459
  · exact ⟨154459, by norm_num, h154459, by omega⟩
  by_cases h183809 : n < 183809
  · exact ⟨183809, by norm_num, h183809, by omega⟩
  exact ⟨218737, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraPrimeChain218737To522059 -/
section


namespace Erdos390.WholePaper

theorem exists_prime_nagura_218737_to_522059 {n : ℕ}
    (hnLower : 218737 ≤ n) (hnUpper : n < 522059) : HasNaguraPrime n := by
  by_cases h260317 : n < 260317
  · exact ⟨260317, by norm_num, h260317, by omega⟩
  by_cases h309779 : n < 309779
  · exact ⟨309779, by norm_num, h309779, by omega⟩
  by_cases h368647 : n < 368647
  · exact ⟨368647, by norm_num, h368647, by omega⟩
  by_cases h438701 : n < 438701
  · exact ⟨438701, by norm_num, h438701, by omega⟩
  exact ⟨522059, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraPrimeChain522059To1046959 -/
section


namespace Erdos390.WholePaper

theorem exists_prime_nagura_522059_to_1046959 {n : ℕ}
    (hnLower : 522059 ≤ n) (hnUpper : n < 1046959) : HasNaguraPrime n := by
  by_cases h621259 : n < 621259
  · exact ⟨621259, by norm_num, h621259, by omega⟩
  by_cases h739301 : n < 739301
  · exact ⟨739301, by norm_num, h739301, by omega⟩
  by_cases h879797 : n < 879797
  · exact ⟨879797, by norm_num, h879797, by omega⟩
  exact ⟨1046959, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraPrimeChain1046959To1482617 -/
section


namespace Erdos390.WholePaper

theorem exists_prime_nagura_1046959_to_1482617 {n : ℕ}
    (hnLower : 1046959 ≤ n) (hnUpper : n < 1482617) : HasNaguraPrime n := by
  by_cases h1245883 : n < 1245883
  · exact ⟨1245883, by norm_num, h1245883, by omega⟩
  exact ⟨1482617, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraPrimeChainTo1482617 -/
section


/-! # Aggregated finite Nagura prime chain to `1482617` -/

namespace Erdos390.WholePaper

theorem exists_prime_nagura_to_1482617 {n : ℕ}
    (hnLower : 91639 ≤ n) (hnUpper : n < 1482617) : HasNaguraPrime n := by
  by_cases h1 : n < 218737
  · exact exists_prime_nagura_91639_to_218737 hnLower h1
  by_cases h2 : n < 522059
  · exact exists_prime_nagura_218737_to_522059 (by omega) h2
  by_cases h3 : n < 1046959
  · exact exists_prime_nagura_522059_to_1046959 (by omega) h3
  · exact exists_prime_nagura_1046959_to_1482617 (by omega) hnUpper

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraPrimeChain1482617To3538187 -/
section


namespace Erdos390.WholePaper

theorem exists_prime_nagura_1482617_to_3538187 {n : ℕ}
    (hnLower : 1482617 ≤ n) (hnUpper : n < 3538187) : HasNaguraPrime n := by
  by_cases h1764319 : n < 1764319
  · exact ⟨1764319, by norm_num, h1764319, by omega⟩
  by_cases h2099543 : n < 2099543
  · exact ⟨2099543, by norm_num, h2099543, by omega⟩
  by_cases h2498521 : n < 2498521
  · exact ⟨2498521, by norm_num, h2498521, by omega⟩
  by_cases h2973251 : n < 2973251
  · exact ⟨2973251, by norm_num, h2973251, by omega⟩
  exact ⟨3538187, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraPrimeChain3538187To8443433 -/
section


namespace Erdos390.WholePaper

theorem exists_prime_nagura_3538187_to_8443433 {n : ℕ}
    (hnLower : 3538187 ≤ n) (hnUpper : n < 8443433) : HasNaguraPrime n := by
  by_cases h4210447 : n < 4210447
  · exact ⟨4210447, by norm_num, h4210447, by omega⟩
  by_cases h5010449 : n < 5010449
  · exact ⟨5010449, by norm_num, h5010449, by omega⟩
  by_cases h5962441 : n < 5962441
  · exact ⟨5962441, by norm_num, h5962441, by omega⟩
  by_cases h7095313 : n < 7095313
  · exact ⟨7095313, by norm_num, h7095313, by omega⟩
  exact ⟨8443433, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraPrimeChain8443433To16000000 -/
section


namespace Erdos390.WholePaper

theorem exists_prime_nagura_8443433_to_16000000 {n : ℕ}
    (hnLower : 8443433 ≤ n) (hnUpper : n < 16000000) : HasNaguraPrime n := by
  by_cases h10047703 : n < 10047703
  · exact ⟨10047703, by norm_num, h10047703, by omega⟩
  by_cases h11956801 : n < 11956801
  · exact ⟨11956801, by norm_num, h11956801, by omega⟩
  by_cases h14228623 : n < 14228623
  · exact ⟨14228623, by norm_num, h14228623, by omega⟩
  exact ⟨16932073, by norm_num, by omega, by omega⟩

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraPrimeChainTo16000000 -/
section


/-! # Aggregated finite Nagura prime chain to `16000000` -/

namespace Erdos390.WholePaper

theorem exists_prime_nagura_1482617_to_16000000 {n : ℕ}
    (hnLower : 1482617 ≤ n) (hnUpper : n < 16000000) :
    HasNaguraPrime n := by
  by_cases h1 : n < 3538187
  · exact exists_prime_nagura_1482617_to_3538187 hnLower h1
  by_cases h2 : n < 8443433
  · exact exists_prime_nagura_3538187_to_8443433 (by omega) h2
  · exact exists_prime_nagura_8443433_to_16000000 (by omega) hnUpper

theorem exists_prime_nagura_91639_to_16000000 {n : ℕ}
    (hnLower : 91639 ≤ n) (hnUpper : n < 16000000) :
    HasNaguraPrime n := by
  by_cases h : n < 1482617
  · exact exists_prime_nagura_to_1482617 hnLower h
  · exact exists_prime_nagura_1482617_to_16000000 (by omega) hnUpper

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraUniversal -/
section


/-! # Nagura's theorem for every natural endpoint -/

namespace Erdos390.WholePaper

/-- For every `n ≥ 25`, there is a prime strictly between `n` and `6n/5`.
This is the public universal Nagura API used by the allocation argument. -/
theorem exists_prime_nagura {n : ℕ} (hn : 25 ≤ n) :
    HasNaguraPrime n := by
  by_cases hSmall : n < 91639
  · exact exists_prime_nagura_below_91639 hn hSmall
  by_cases hFinite : n < 16000000
  · exact exists_prime_nagura_91639_to_16000000 (by omega) hFinite
  · exact exists_prime_nagura_analytic_tail (by omega)

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.NaguraLeastPrimeCorollary -/
section


/-! # Least-prime consequences of the universal Nagura theorem -/

namespace Erdos390.WholePaper



/-- Consecutive primes above the Nagura cutoff have ratio below `6/5`. -/
theorem consecutivePrimes_ratio {pPrev p : ℕ}
    (hConsecutive : pPrev.Prime ∧ p.Prime ∧ pPrev < p ∧
      ∀ q : ℕ, q.Prime → pPrev < q → q < p → False)
    (hpPrevLower : 25 ≤ pPrev) :
    5 * p < 6 * pPrev := by
  obtain ⟨_hPrevPrime, _hpPrime, hPrevLt, hNoBetween⟩ := hConsecutive
  have hLeast : ∀ q : ℕ, q.Prime → pPrev < q → p ≤ q := by
    intro q hqPrime hPrevQ
    by_contra hqp
    exact hNoBetween q hqPrime hPrevQ (by omega)
  exact consecutivePrime_ratio_of_naguraWitness hLeast
    (exists_prime_nagura hpPrevLower)

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.InfiniteAllocation -/
section


/-!
# The exact infinite cofactor allocation

This file instantiates the finite certificate plus least-prime tail and
proves every prime-capacity inequality in Lemma 4.2.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

theorem tsum_tailPrimeRowLoad_eq_zero_of_le_two_hundred
    {ℓ : ℕ} (hℓ : ℓ ≤ 200) :
    (∑' r : ℕ, tailPrimeRowLoad ℓ r) = 0 := by
  rw [tsum_tailPrimeRowLoad_eq]
  apply Finset.sum_eq_zero
  intro r hr
  have hrange := Finset.mem_Icc.mp hr
  omega

/-- Every prime receives at most its exact paper capacity. -/
theorem infiniteAllocation_prime_capacity {ℓ : ℕ} (hℓPrime : ℓ.Prime) :
    allocationPrimeLoad infiniteAllocation ℓ ≤
      C0Rat / (((ℓ - 1 : ℕ) : ℚ)) := by
  by_cases hℓ200 : ℓ ≤ 200
  · rw [allocationPrimeLoad_infiniteAllocation_eq,
      tsum_tailPrimeRowLoad_eq_zero_of_le_two_hundred hℓ200, add_zero]
    exact finiteAllocation_prime_capacity hℓPrime (by omega)
  by_cases hℓ401 : ℓ ≤ 401
  · have hℓ201 : 201 < ℓ := by
      by_contra hnot
      have hEq : ℓ = 201 := by omega
      subst ℓ
      norm_num at hℓPrime
    obtain ⟨hPrevPrime, hPrevℓ, hNoBetween⟩ :=
      previousPrime_spec (by omega : 2 < ℓ)
    rw [allocationPrimeLoad_infiniteAllocation_eq,
      tsum_tailPrimeRowLoad_eq_consecutiveBlock hPrevPrime hℓPrime
        hPrevℓ hNoBetween]
    exact finiteAllocation_prime_overlap hℓPrime hℓ201 hℓ401
  · have hℓGt : 401 < ℓ := by omega
    obtain ⟨hPrevPrime, hPrevℓ, hNoBetween⟩ :=
      previousPrime_spec (by omega : 2 < ℓ)
    have hPrev401 : 401 ≤ previousPrime ℓ := by
      by_contra hnot
      exact hNoBetween 401 (by norm_num) (by omega) (by omega)
    have hRatio : 5 * ℓ < 6 * previousPrime ℓ :=
      consecutivePrimes_ratio
        ⟨hPrevPrime, hℓPrime, hPrevℓ, hNoBetween⟩ (by omega)
    have hBlock := allocationTail_block_capacity_lt_C0Rat
      hPrevPrime.pos hPrevℓ hRatio
    rw [allocationPrimeLoad_infiniteAllocation_eq,
      finitePrimeLoad_eq_zero_of_gt_401 hℓGt, zero_add,
      tsum_tailPrimeRowLoad_eq_consecutiveBlock hPrevPrime hℓPrime
        hPrevℓ hNoBetween,
      max_eq_right (by omega : 201 ≤ previousPrime ℓ)]
    apply le_of_lt
    have hDenom : (0 : ℚ) < ((ℓ - 1 : ℕ) : ℚ) := by
      exact_mod_cast (by omega : 0 < ℓ - 1)
    apply (lt_div_iff₀ hDenom).2
    simpa only [mul_comm] using hBlock



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.FinitePrefixAllocationCapacity -/
section


/-!
# Capacity of every fixed prefix of the infinite allocation

The stationary-anchor construction realizes finitely many rows of the exact
infinite allocation.  This file proves that their literal weighted load is
bounded by the already certified full load.  No limiting argument occurs
here; it is finite-sum and summability algebra over the concrete allocation.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



theorem allocationPrimeRowLoad_infiniteAllocation_nonneg (ℓ r : ℕ) :
    0 ≤ allocationPrimeRowLoad infiniteAllocation ℓ r := by
  apply Finset.sum_nonneg
  intro q _hq
  exact mul_nonneg (Nat.cast_nonneg _) (infiniteAllocation_nonneg r q)

theorem summable_allocationPrimeRowLoad_infiniteAllocation (ℓ : ℕ) :
    Summable (allocationPrimeRowLoad infiniteAllocation ℓ) := by
  have hadd := (summable_finitePrimeRowLoad ℓ).add
    (summable_tailPrimeRowLoad ℓ)
  exact hadd.congr fun r ↦ (infinitePrimeRowLoad_eq_add ℓ r).symm

/-- A fixed prefix cannot use more of a prime coordinate than the full
nonnegative infinite allocation. -/
theorem prefixAllocationPrimeLoad_le_full (R ℓ : ℕ) :
    prefixAllocationPrimeLoad R ℓ ≤
      allocationPrimeLoad infiniteAllocation ℓ := by
  rw [prefixAllocationPrimeLoad, allocationPrimeLoad]
  exact (summable_allocationPrimeRowLoad_infiniteAllocation ℓ).sum_le_tsum
    (Finset.Icc 1 R)
    (fun r _hr ↦ allocationPrimeRowLoad_infiniteAllocation_nonneg ℓ r)



/-- Every finite prefix inherits the paper's exact certified capacity. -/
theorem prefixAllocationPrimeLoad_le_capacity
    (R : ℕ) {ℓ : ℕ} (hℓPrime : ℓ.Prime) :
    prefixAllocationPrimeLoad R ℓ ≤
      C0Rat / (((ℓ - 1 : ℕ) : ℚ)) := by
  exact (prefixAllocationPrimeLoad_le_full R ℓ).trans
    (infiniteAllocation_prime_capacity hℓPrime)

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.ExactFinitePartition -/
section


/-!
# Exact finite partitions with prescribed part sizes

This module is independent of the asymptotic allocation argument. It turns
finite target counts into actual disjoint Finset parts and an explicit
remainder.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



/-- Core finite allocation: prescribed counts whose sum fits in the source
can be realized by pairwise disjoint subsets. -/
theorem exists_pairwiseDisjoint_finset_parts
    {α ι : Type*} [DecidableEq α]
    (source : Finset α) (indices : Finset ι) (count : ι → ℕ)
    (hcount : ∑ i ∈ indices, count i ≤ source.card) :
    ∃ parts : ι → Finset α,
      (∀ i ∈ indices, parts i ⊆ source) ∧
      (indices : Set ι).PairwiseDisjoint parts ∧
      (∀ i ∈ indices, (parts i).card = count i) := by
  classical
  induction indices using Finset.induction_on generalizing source with
  | empty =>
      refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
      · simp
      · intro i hi
        simp at hi
      · simp
  | @insert a indices ha ih =>
      have haCount : count a ≤ source.card := by
        calc
          count a ≤ count a + ∑ i ∈ indices, count i := Nat.le_add_right _ _
          _ = ∑ i ∈ insert a indices, count i := by simp [ha]
          _ ≤ source.card := hcount
      obtain ⟨part, hpartSource, hpartCard⟩ :=
        Finset.exists_subset_card_eq haCount
      have hrestCount :
          ∑ i ∈ indices, count i ≤ (source \ part).card := by
        rw [Finset.card_sdiff_of_subset hpartSource, hpartCard]
        rw [Finset.sum_insert ha] at hcount
        omega
      obtain ⟨parts, hpartsSubset, hpartsDisjoint, hpartsCard⟩ :=
        ih (source := source \ part) hrestCount
      let newParts : ι → Finset α := Function.update parts a part
      refine ⟨newParts, ?_, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · simpa [newParts] using hpartSource
        · have hiSubset := hpartsSubset i hi
          have hine : i ≠ a := ne_of_mem_of_not_mem hi ha
          simpa [newParts, hine] using
            (hiSubset.trans (Finset.sdiff_subset : source \ part ⊆ source))
      · intro i hi j hj hij
        simp only [Finset.mem_coe, Finset.mem_insert] at hi hj
        by_cases hia : i = a
        · subst i
          have hjne : j ≠ a := hij.symm
          have hjIndices : j ∈ indices := hj.resolve_left hjne
          change Disjoint (newParts a) (newParts j)
          rw [show newParts a = part by simp [newParts],
            show newParts j = parts j by simp [newParts, hjne]]
          rw [Finset.disjoint_left]
          intro x hxpart hxj
          have hxrest := hpartsSubset j hjIndices hxj
          exact (Finset.mem_sdiff.mp hxrest).2 hxpart
        · by_cases hja : j = a
          · subst j
            have hiIndices : i ∈ indices := hi.resolve_left hia
            change Disjoint (newParts i) (newParts a)
            rw [show newParts i = parts i by simp [newParts, hia],
              show newParts a = part by simp [newParts]]
            rw [Finset.disjoint_left]
            intro x hxi hxpart
            have hxrest := hpartsSubset i hiIndices hxi
            exact (Finset.mem_sdiff.mp hxrest).2 hxpart
          · have hiIndices : i ∈ indices := hi.resolve_left hia
            have hjIndices : j ∈ indices := hj.resolve_left hja
            change Disjoint (newParts i) (newParts j)
            rw [show newParts i = parts i by simp [newParts, hia],
              show newParts j = parts j by simp [newParts, hja]]
            exact hpartsDisjoint hiIndices hjIndices hij
      · intro i hi
        simp only [Finset.mem_insert] at hi
        by_cases hia : i = a
        · subst i
          simpa [newParts] using hpartCard
        · have hiIndices : i ∈ indices := hi.resolve_left hia
          simpa [newParts, hia] using
            hpartsCard i hiIndices

/-- Terminal finite partition theorem, including the explicit remainder and
all union/cardinality identities used by later anchor constructions. -/
theorem exists_exactFinitePartition
    {α ι : Type*} [DecidableEq α]
    (source : Finset α) (indices : Finset ι) (count : ι → ℕ)
    (hcount : ∑ i ∈ indices, count i ≤ source.card) :
    Nonempty (ExactFinitePartition source indices count) := by
  classical
  obtain ⟨parts, hpartsSubset, hpartsDisjoint, hpartsCard⟩ :=
    exists_pairwiseDisjoint_finset_parts source indices count hcount
  let union : Finset α := indices.biUnion parts
  let remainder : Finset α := source \ union
  have hunionSubset : union ⊆ source := by
    intro x hx
    simp only [union, Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact hpartsSubset i hi hxi
  have hunionCard :
      union.card = ∑ i ∈ indices, count i := by
    calc
      union.card = ∑ i ∈ indices, (parts i).card := by
        exact Finset.card_biUnion hpartsDisjoint
      _ = ∑ i ∈ indices, count i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hpartsCard i hi
  refine ⟨{
    parts := parts
    remainder := remainder
    parts_subset := hpartsSubset
    parts_card := hpartsCard
    parts_pairwiseDisjoint := hpartsDisjoint
    remainder_subset := Finset.sdiff_subset
    part_remainder_disjoint := ?_
    union_remainder := ?_
    union_card := hunionCard
    remainder_card := ?_
  }⟩
  · intro i hi
    apply Finset.disjoint_left.mpr
    intro x hxi hxremainder
    have hxiUnion : x ∈ union := by
      simp only [union, Finset.mem_biUnion]
      exact ⟨i, hi, hxi⟩
    exact (Finset.mem_sdiff.mp hxremainder).2 hxiUnion
  · exact Finset.union_sdiff_of_subset hunionSubset
  · change (source \ union).card =
      source.card - ∑ i ∈ indices, count i
    rw [Finset.card_sdiff_of_subset hunionSubset, hunionCard]



theorem sum_distinguishedRemainderCount
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (distinguished : ι) (rawCount : ι → ℕ)
    (total : ℕ) (hdistinguished : distinguished ∈ indices)
    (hraw : ∑ j ∈ indices.erase distinguished, rawCount j ≤ total) :
    ∑ i ∈ indices,
        distinguishedRemainderCount indices distinguished rawCount total i =
      total := by
  classical
  have herase :
      ∑ i ∈ indices.erase distinguished,
          distinguishedRemainderCount indices distinguished rawCount total i =
        ∑ i ∈ indices.erase distinguished, rawCount i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [distinguishedRemainderCount]
    rw [if_neg]
    exact Finset.ne_of_mem_erase hi
  calc
    ∑ i ∈ indices,
        distinguishedRemainderCount indices distinguished rawCount total i =
        (∑ i ∈ indices.erase distinguished,
            distinguishedRemainderCount indices distinguished rawCount total i) +
          distinguishedRemainderCount indices distinguished rawCount total
            distinguished :=
      (Finset.sum_erase_add indices _ hdistinguished).symm
    _ = (∑ i ∈ indices.erase distinguished, rawCount i) +
        (total - ∑ i ∈ indices.erase distinguished, rawCount i) := by
      rw [herase]
      simp [distinguishedRemainderCount]
    _ = total := Nat.add_sub_of_le hraw

/-- Distinguished-coordinate form of the terminal partition theorem. -/
theorem exists_exactFinitePartition_distinguishedRemainder
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (source : Finset α) (indices : Finset ι) (distinguished : ι)
    (rawCount : ι → ℕ) (hdistinguished : distinguished ∈ indices)
    (hraw :
      ∑ j ∈ indices.erase distinguished, rawCount j ≤ source.card) :
    Nonempty (ExactFinitePartition source indices
      (distinguishedRemainderCount indices distinguished rawCount
        source.card)) := by
  apply exists_exactFinitePartition
  rw [sum_distinguishedRemainderCount indices distinguished rawCount
    source.card hdistinguished hraw]





/-- A real budget inequality implies that all scaled floor counts fit in
the corresponding natural-number budget. -/
theorem sum_scaledFloorCount_le
    {ι : Type*} [DecidableEq ι]
    (indices : Finset ι) (scale : ℝ) (weight : ι → ℝ) (total : ℕ)
    (hscale : 0 ≤ scale)
    (hweight : ∀ i ∈ indices, 0 ≤ weight i)
    (hbudget :
      scale * ∑ i ∈ indices, weight i ≤ (total : ℝ)) :
    ∑ i ∈ indices, scaledFloorCount scale weight i ≤ total := by
  have hreal :
      ((∑ i ∈ indices, scaledFloorCount scale weight i : ℕ) : ℝ) ≤
        (total : ℝ) := by
    calc
      ((∑ i ∈ indices, scaledFloorCount scale weight i : ℕ) : ℝ) =
          ∑ i ∈ indices, (scaledFloorCount scale weight i : ℝ) := by
        simp
      _ ≤ ∑ i ∈ indices, scale * weight i := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.floor_le (mul_nonneg hscale (hweight i hi))
      _ = scale * ∑ i ∈ indices, weight i := by
        rw [Finset.mul_sum]
      _ ≤ (total : ℝ) := hbudget
  exact_mod_cast hreal



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.StationaryPrefixRealization -/
section


/-!
# Exact realization of a fixed stationary prefix

For a fixed row, this module realizes every positive coordinate of the
infinite allocation by an actual part of the stationary prime layer.
Non-distinguished coordinates are rounded down at the second-order scale;
one fixed positive coordinate absorbs the complete rounding remainder.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section









/-- The real-valued positive-support mass is the cast of alpha r. -/
theorem infiniteAllocationPositiveSupport_sum_real
    (r : ℕ) (hr : 1 ≤ r) :
    (∑ q ∈ infiniteAllocationPositiveSupport r,
        (infiniteAllocation r q : ℝ)) = (alpha r : ℝ) := by
  simpa only [Rat.cast_sum] using
    congrArg (fun x : ℚ ↦ (x : ℝ))
      (infiniteAllocationPositiveSupport_sum r hr)

/-- A positive distinguished coordinate leaves strict mass slack after it
is erased from the row support. -/
theorem infiniteAllocationPositiveSupport_erase_sum_lt
    (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r) :
    (∑ q ∈ (infiniteAllocationPositiveSupport r).erase distinguished,
        (infiniteAllocation r q : ℝ)) < (alpha r : ℝ) := by
  have hdistinguishedPositive :
      0 < (infiniteAllocation r distinguished : ℝ) := by
    exact_mod_cast
      (mem_infiniteAllocationPositiveSupport.mp hdistinguished).2
  have hsplit :
      (∑ q ∈ (infiniteAllocationPositiveSupport r).erase distinguished,
          (infiniteAllocation r q : ℝ)) +
          (infiniteAllocation r distinguished : ℝ) =
        (alpha r : ℝ) := by
    calc
      (∑ q ∈ (infiniteAllocationPositiveSupport r).erase distinguished,
          (infiniteAllocation r q : ℝ)) +
          (infiniteAllocation r distinguished : ℝ) =
          ∑ q ∈ infiniteAllocationPositiveSupport r,
            (infiniteAllocation r q : ℝ) :=
        Finset.sum_erase_add _ _ hdistinguished
      _ = (alpha r : ℝ) :=
        infiniteAllocationPositiveSupport_sum_real r hr
  exact (lt_add_of_pos_right _ hdistinguishedPositive).trans_eq hsplit





theorem stationaryPrefixCount_eq_raw_of_ne
    {n r distinguished q : ℕ} (hq : q ≠ distinguished) :
    stationaryPrefixCount n r distinguished q =
      stationaryPrefixRawCount n r q := by
  simp only [stationaryPrefixCount, distinguishedRemainderCount, hq,
    if_false]

theorem stationaryPrefixCount_eq_remainder
    (n r distinguished : ℕ) :
    stationaryPrefixCount n r distinguished distinguished =
      (stationaryPrimeLayer n r).card -
        ∑ q ∈ (infiniteAllocationPositiveSupport r).erase distinguished,
          stationaryPrefixRawCount n r q := by
  simp only [stationaryPrefixCount, distinguishedRemainderCount, if_pos]

/-- Each unadjusted floor has the intended normalized limit. -/
theorem stationaryPrefixRawCount_normalized_tendsto
    (r q : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        (stationaryPrefixRawCount n r q : ℝ) /
          secondOrderScale n)
      atTop (nhds (infiniteAllocation r q : ℝ)) := by
  have hweight : 0 ≤ (infiniteAllocation r q : ℝ) := by
    exact_mod_cast infiniteAllocation_nonneg r q
  have hfloor :=
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) hweight).comp
      secondOrderScale_tendsto_atTop
  apply hfloor.congr'
  exact Eventually.of_forall fun n ↦ by
    simp only [Function.comp_apply, stationaryPrefixRawCount,
      scaledFloorCount]
    rw [mul_comm]

/-- Strict distinguished mass slack and the layer-cardinality asymptotic
make all non-distinguished floor targets fit eventually. -/
theorem eventually_stationaryPrefixRawCount_sum_le
    (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r) :
    ∀ᶠ n : ℕ in atTop,
      (∑ q ∈ (infiniteAllocationPositiveSupport r).erase distinguished,
          stationaryPrefixRawCount n r q) ≤
        (stationaryPrimeLayer n r).card := by
  have hcard :
      Tendsto
        (fun n : ℕ ↦
          ((stationaryPrimeLayer n r).card : ℝ) /
            secondOrderScale n)
        atTop (nhds (alpha r : ℝ)) := by
    simpa only [secondOrderScale] using
      stationaryPrimeLayer_card_normalized_tendsto r hr
  have hgap :=
    infiniteAllocationPositiveSupport_erase_sum_lt
      r distinguished hr hdistinguished
  have hratio := hcard.eventually (eventually_gt_nhds hgap)
  filter_upwards [hratio, eventually_secondOrderScale_pos] with n
    hratioN hscale
  apply sum_scaledFloorCount_le
    ((infiniteAllocationPositiveSupport r).erase distinguished)
    (secondOrderScale n)
    (fun q ↦ (infiniteAllocation r q : ℝ))
    (stationaryPrimeLayer n r).card hscale.le
  · intro q _hq
    exact_mod_cast infiniteAllocation_nonneg r q
  · have hstrict :
        secondOrderScale n *
            (∑ q ∈
              (infiniteAllocationPositiveSupport r).erase distinguished,
              (infiniteAllocation r q : ℝ)) <
          ((stationaryPrimeLayer n r).card : ℝ) := by
      have hmul := (lt_div_iff₀ hscale).mp hratioN
      simpa only [mul_comm] using hmul
    exact hstrict.le



/-- The absorbing distinguished count has its intended normalized limit. -/
theorem stationaryPrefixCount_distinguished_normalized_tendsto
    (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r) :
    Tendsto
      (fun n : ℕ ↦
        (stationaryPrefixCount n r distinguished distinguished : ℝ) /
          secondOrderScale n)
      atTop
      (nhds (infiniteAllocation r distinguished : ℝ)) := by
  have hcard :
      Tendsto
        (fun n : ℕ ↦
          ((stationaryPrimeLayer n r).card : ℝ) /
            secondOrderScale n)
        atTop (nhds (alpha r : ℝ)) := by
    simpa only [secondOrderScale] using
      stationaryPrimeLayer_card_normalized_tendsto r hr
  have hfloorSum :
      Tendsto
        (fun n : ℕ ↦
          ∑ q ∈
            (infiniteAllocationPositiveSupport r).erase distinguished,
            (stationaryPrefixRawCount n r q : ℝ) /
              secondOrderScale n)
        atTop
        (nhds
          (∑ q ∈
            (infiniteAllocationPositiveSupport r).erase distinguished,
            (infiniteAllocation r q : ℝ))) := by
    apply tendsto_finset_sum
    intro q _hq
    exact stationaryPrefixRawCount_normalized_tendsto r q
  have hlimit :
      (alpha r : ℝ) -
          (∑ q ∈
            (infiniteAllocationPositiveSupport r).erase distinguished,
            (infiniteAllocation r q : ℝ)) =
        (infiniteAllocation r distinguished : ℝ) := by
    have hsplit :
        (∑ q ∈
          (infiniteAllocationPositiveSupport r).erase distinguished,
          (infiniteAllocation r q : ℝ)) +
            (infiniteAllocation r distinguished : ℝ) =
          (alpha r : ℝ) := by
      calc
        (∑ q ∈
          (infiniteAllocationPositiveSupport r).erase distinguished,
          (infiniteAllocation r q : ℝ)) +
            (infiniteAllocation r distinguished : ℝ) =
            ∑ q ∈ infiniteAllocationPositiveSupport r,
              (infiniteAllocation r q : ℝ) :=
          Finset.sum_erase_add _ _ hdistinguished
        _ = (alpha r : ℝ) :=
          infiniteAllocationPositiveSupport_sum_real r hr
    rw [← hsplit]
    ring
  have hdifference := hcard.sub hfloorSum
  rw [hlimit] at hdifference
  apply hdifference.congr'
  filter_upwards [
    eventually_stationaryPrefixRawCount_sum_le
      r distinguished hr hdistinguished] with n hfit
  rw [stationaryPrefixCount_eq_remainder]
  rw [Nat.cast_sub hfit, Nat.cast_sum]
  rw [← Finset.sum_div]
  ring

/-- Every positive coordinate, including the absorbing one, has the
prescribed normalized cardinality. -/
theorem stationaryPrefixCount_normalized_tendsto
    (r distinguished q : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r)
    (_hq : q ∈ infiniteAllocationPositiveSupport r) :
    Tendsto
      (fun n : ℕ ↦
        (stationaryPrefixCount n r distinguished q : ℝ) /
          secondOrderScale n)
      atTop (nhds (infiniteAllocation r q : ℝ)) := by
  by_cases hqd : q = distinguished
  · subst q
    exact stationaryPrefixCount_distinguished_normalized_tendsto
      r distinguished hr hdistinguished
  · apply (stationaryPrefixRawCount_normalized_tendsto r q).congr'
    exact Eventually.of_forall fun n ↦ by
      change
        (stationaryPrefixRawCount n r q : ℝ) / secondOrderScale n =
          (stationaryPrefixCount n r distinguished q : ℝ) /
            secondOrderScale n
      rw [stationaryPrefixCount_eq_raw_of_ne hqd]



/-- Eventually the exact target counts are realized by an exhaustive
partition of the stationary layer. -/
theorem eventually_stationaryPrefixPartition_nonempty
    (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r) :
    ∀ᶠ n : ℕ in atTop,
      Nonempty (StationaryPrefixPartition n r distinguished) := by
  filter_upwards [
    eventually_stationaryPrefixRawCount_sum_le
      r distinguished hr hdistinguished] with n hfit
  obtain ⟨partition⟩ :=
    exists_exactFinitePartition_distinguishedRemainder
      (stationaryPrimeLayer n r)
      (infiniteAllocationPositiveSupport r) distinguished
      (stationaryPrefixRawCount n r) hdistinguished hfit
  have hsum :
      (∑ q ∈ infiniteAllocationPositiveSupport r,
          stationaryPrefixCount n r distinguished q) =
        (stationaryPrimeLayer n r).card :=
    sum_distinguishedRemainderCount
      (infiniteAllocationPositiveSupport r) distinguished
      (stationaryPrefixRawCount n r) (stationaryPrimeLayer n r).card
      hdistinguished hfit
  have hremainderCard : partition.remainder.card = 0 := by
    rw [partition.remainder_card]
    simpa only [stationaryPrefixCount, Nat.sub_self] using
      congrArg
        (fun total ↦ (stationaryPrimeLayer n r).card - total)
        hsum
  have hremainder : partition.remainder = ∅ :=
    Finset.card_eq_zero.mp hremainderCard
  refine ⟨{
    parts := partition.parts
    parts_subset := partition.parts_subset
    parts_card := ?_
    parts_pairwiseDisjoint := partition.parts_pairwiseDisjoint
    union_parts := ?_
  }⟩
  · intro q hq
    simpa only [stationaryPrefixCount] using partition.parts_card q hq
  · simpa only [hremainder, Finset.union_empty] using
      partition.union_remainder

/-- Terminal fixed-row realization: one family of actual parts is
eventually exhaustive and disjoint, and every positive part has the exact
rational asymptotic weight. -/
theorem exists_stationaryPrefixParts
    (r distinguished : ℕ) (hr : 1 ≤ r)
    (hdistinguished :
      distinguished ∈ infiniteAllocationPositiveSupport r) :
    ∃ parts : ℕ → ℕ → Finset ℕ,
      (∀ᶠ n : ℕ in atTop,
        (∀ q ∈ infiniteAllocationPositiveSupport r,
          parts n q ⊆ stationaryPrimeLayer n r) ∧
        (∀ q ∈ infiniteAllocationPositiveSupport r,
          (parts n q).card =
            stationaryPrefixCount n r distinguished q) ∧
        (infiniteAllocationPositiveSupport r : Set ℕ).PairwiseDisjoint
          (parts n) ∧
        (infiniteAllocationPositiveSupport r).biUnion (parts n) =
          stationaryPrimeLayer n r) ∧
      ∀ q ∈ infiniteAllocationPositiveSupport r,
        Tendsto
          (fun n : ℕ ↦
            ((parts n q).card : ℝ) / secondOrderScale n)
          atTop (nhds (infiniteAllocation r q : ℝ)) := by
  classical
  let parts : ℕ → ℕ → Finset ℕ := fun n ↦
    if h : Nonempty (StationaryPrefixPartition n r distinguished) then
      (Classical.choice h).parts
    else
      fun _ ↦ ∅
  have hexists :=
    eventually_stationaryPrefixPartition_nonempty
      r distinguished hr hdistinguished
  have hparts :
      ∀ᶠ n : ℕ in atTop,
        (∀ q ∈ infiniteAllocationPositiveSupport r,
          parts n q ⊆ stationaryPrimeLayer n r) ∧
        (∀ q ∈ infiniteAllocationPositiveSupport r,
          (parts n q).card =
            stationaryPrefixCount n r distinguished q) ∧
        (infiniteAllocationPositiveSupport r : Set ℕ).PairwiseDisjoint
          (parts n) ∧
        (infiniteAllocationPositiveSupport r).biUnion (parts n) =
          stationaryPrimeLayer n r := by
    filter_upwards [hexists] with n hn
    have hpartsEq :
        parts n = (Classical.choice hn).parts := by
      dsimp only [parts]
      rw [dif_pos hn]
    rw [hpartsEq]
    exact ⟨(Classical.choice hn).parts_subset,
      (Classical.choice hn).parts_card,
      (Classical.choice hn).parts_pairwiseDisjoint,
      (Classical.choice hn).union_parts⟩
  refine ⟨parts, hparts, ?_⟩
  intro q hq
  apply
    (stationaryPrefixCount_normalized_tendsto
      r distinguished q hr hdistinguished hq).congr'
  filter_upwards [hparts] with n hn
  rw [hn.2.1 q hq]

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.StationaryPrefixAnchors -/
section


/-!
# Simultaneous fixed-prefix rows and their central anchors

The analytic realization is first made simultaneous over an arbitrary
finite set of fixed rows.  For one realized row, the marked pairs
(cofactor, prime) are then sent to the literal anchor prime times cofactor.
The map is injective once the stationary primes exceed the cofactor range,
and its finite product splits exactly into marker and cofactor products.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Any finite collection of fixed positive rows can be realized
simultaneously by a single family of stationary-layer partitions. -/
theorem exists_stationaryPrefixParts_on_finset
    (rows : Finset ℕ)
    (hrows : ∀ r ∈ rows, 1 ≤ r)
    (distinguished : ℕ → ℕ)
    (hdistinguished :
      ∀ r ∈ rows,
        distinguished r ∈ infiniteAllocationPositiveSupport r) :
    ∃ parts :
        ℕ → {r // r ∈ rows} → ℕ → Finset ℕ,
      (∀ᶠ n : ℕ in atTop,
        ∀ r : {r // r ∈ rows},
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            parts n r q ⊆ stationaryPrimeLayer n r.1) ∧
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            (parts n r q).card =
              stationaryPrefixCount n r.1 (distinguished r.1) q) ∧
          (infiniteAllocationPositiveSupport r.1 :
            Set ℕ).PairwiseDisjoint (parts n r) ∧
          (infiniteAllocationPositiveSupport r.1).biUnion
              (parts n r) =
            stationaryPrimeLayer n r.1) ∧
      ∀ r : {r // r ∈ rows},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ)) := by
  have hexists (r : {r // r ∈ rows}) :=
    exists_stationaryPrefixParts r.1 (distinguished r.1)
      (hrows r.1 r.2) (hdistinguished r.1 r.2)
  choose rowParts hrowParts hrowLimit using hexists
  let parts : ℕ → {r // r ∈ rows} → ℕ → Finset ℕ :=
    fun n r q ↦ rowParts r n q
  refine ⟨parts, ?_, ?_⟩
  · rw [Filter.eventually_all]
    intro r
    simpa only [parts] using hrowParts r
  · intro r q hq
    simpa only [parts] using hrowLimit r q hq

























end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.StationaryPrefixValuationAsymptotic -/
section


/-!
# Valuation asymptotic of the actual fixed-prefix cofactor product

The cofactor product in this file is the literal product of the cofactors
attached to all realized marker primes in rows one through R.  Its exact
factorization is reduced to the actual part cardinalities, whose already
proved limits give the certified finite-prefix allocation load.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Exact valuation of the cofactor product in one realized row. -/
theorem stationaryPrefixCofactorProduct_factorization
    {r ell : ℕ} (parts : ℕ → Finset ℕ) :
    (stationaryPrefixCofactorProduct r parts).factorization ell =
      ∑ q ∈ infiniteAllocationPositiveSupport r,
        (parts q).card * q.factorization ell := by
  rw [stationaryPrefixCofactorProduct,
    Nat.factorization_prod_apply]
  · rw [stationaryPrefixMarkedPairs, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q _hq
    simp
  · intro x hx
    have hxmem := Finset.mem_sigma.mp hx
    have hqLower :=
      (Finset.mem_Icc.mp
        (mem_infiniteAllocationPositiveSupport.mp hxmem.1).1).1
    omega

theorem stationaryPrefixCofactorProduct_pos
    {r : ℕ} (parts : ℕ → Finset ℕ) :
    0 < stationaryPrefixCofactorProduct r parts := by
  apply Finset.prod_pos
  intro x hx
  have hxmem := Finset.mem_sigma.mp hx
  have hqLower :=
    (Finset.mem_Icc.mp
      (mem_infiniteAllocationPositiveSupport.mp hxmem.1).1).1
  omega

/-- Weighted summation over the positive support is exactly the concrete
allocation row load. -/
theorem sum_infiniteAllocationPositiveSupport_factorization_eq
    (r ell : ℕ) :
    (∑ q ∈ infiniteAllocationPositiveSupport r,
        (q.factorization ell : ℚ) * infiniteAllocation r q) =
      allocationPrimeRowLoad infiniteAllocation ell r := by
  rw [allocationPrimeRowLoad]
  apply Finset.sum_subset
  · intro q hq
    exact (mem_infiniteAllocationPositiveSupport.mp hq).1
  · intro q hq hqNotSupport
    have hnotPos : ¬0 < infiniteAllocation r q := by
      intro hpos
      exact hqNotSupport
        (mem_infiniteAllocationPositiveSupport.mpr ⟨hq, hpos⟩)
    have hzero : infiniteAllocation r q = 0 :=
      le_antisymm (not_lt.mp hnotPos) (infiniteAllocation_nonneg r q)
    simp only [hzero, mul_zero]

/-- The factorization of one actual row cofactor product has the exact
allocation row-load limit. -/
theorem stationaryPrefixCofactorProduct_factorization_normalized_tendsto
    (r ell : ℕ)
    (parts : ℕ → ℕ → Finset ℕ)
    (hparts :
      ∀ q ∈ infiniteAllocationPositiveSupport r,
        Tendsto
          (fun n : ℕ ↦
            ((parts n q).card : ℝ) / secondOrderScale n)
          atTop (nhds (infiniteAllocation r q : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        (((stationaryPrefixCofactorProduct r (parts n)).factorization
          ell : ℕ) : ℝ) / secondOrderScale n)
      atTop
      (nhds (allocationPrimeRowLoad infiniteAllocation ell r : ℝ)) := by
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          ∑ q ∈ infiniteAllocationPositiveSupport r,
            (q.factorization ell : ℝ) *
              (((parts n q).card : ℝ) / secondOrderScale n))
        atTop
        (nhds
          (∑ q ∈ infiniteAllocationPositiveSupport r,
            (q.factorization ell : ℝ) *
              (infiniteAllocation r q : ℝ))) := by
    apply tendsto_finset_sum
    intro q hq
    exact (hparts q hq).const_mul (q.factorization ell : ℝ)
  have hmass :
      (∑ q ∈ infiniteAllocationPositiveSupport r,
          (q.factorization ell : ℝ) *
            (infiniteAllocation r q : ℝ)) =
        (allocationPrimeRowLoad infiniteAllocation ell r : ℝ) := by
    exact_mod_cast
      sum_infiniteAllocationPositiveSupport_factorization_eq r ell
  rw [hmass] at hsum
  apply hsum.congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp only
    rw [stationaryPrefixCofactorProduct_factorization,
      Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q _hq
    push_cast
    ring



/-- Exact factorization of the finite-row product as the sum of the exact
row-product factorizations. -/
theorem stationaryPrefixCofactorProductUpTo_factorization
    (R ell : ℕ)
    (parts :
      {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ) :
    (stationaryPrefixCofactorProductUpTo R parts).factorization ell =
      ∑ r : {r // r ∈ Finset.Icc 1 R},
        (stationaryPrefixCofactorProduct r.1
          (parts r)).factorization ell := by
  rw [stationaryPrefixCofactorProductUpTo,
    Nat.factorization_prod_apply]
  intro r _hr
  exact (stationaryPrefixCofactorProduct_pos (parts r)).ne'

/-- The finite subtype sum of row loads is the literal prefix load. -/
theorem sum_allocationPrimeRowLoad_subtype_eq_prefix
    (R ell : ℕ) :
    (∑ r : {r // r ∈ Finset.Icc 1 R},
        allocationPrimeRowLoad infiniteAllocation ell r.1) =
      prefixAllocationPrimeLoad R ell := by
  rw [prefixAllocationPrimeLoad]
  change
    (∑ r : {r // r ∈ Finset.Icc 1 R},
      allocationPrimeRowLoad infiniteAllocation ell r.1) =
      ∑ r ∈ Finset.Icc 1 R,
        allocationPrimeRowLoad infiniteAllocation ell r
  simpa only [Finset.univ_eq_attach] using
    (Finset.sum_attach (Finset.Icc 1 R)
      (fun r ↦ allocationPrimeRowLoad infiniteAllocation ell r))

/-- The factorization of the actual finite-row cofactor product converges
to the certified concrete prefix allocation load. -/
theorem stationaryPrefixCofactorProductUpTo_factorization_normalized_tendsto
    (R ell : ℕ)
    (parts :
      ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ)
    (hparts :
      ∀ r : {r // r ∈ Finset.Icc 1 R},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        (((stationaryPrefixCofactorProductUpTo R
          (parts n)).factorization ell : ℕ) : ℝ) /
            secondOrderScale n)
      atTop (nhds (prefixAllocationPrimeLoad R ell : ℝ)) := by
  have hrows :
      Tendsto
        (fun n : ℕ ↦
          ∑ r : {r // r ∈ Finset.Icc 1 R},
            (((stationaryPrefixCofactorProduct r.1
              (parts n r)).factorization ell : ℕ) : ℝ) /
                secondOrderScale n)
        atTop
        (nhds
          (∑ r : {r // r ∈ Finset.Icc 1 R},
            (allocationPrimeRowLoad infiniteAllocation ell r.1 : ℝ))) := by
    apply tendsto_finset_sum
    intro r _hr
    exact
      stationaryPrefixCofactorProduct_factorization_normalized_tendsto
        r.1 ell (fun n q ↦ parts n r q) (hparts r)
  have hmass :
      (∑ r : {r // r ∈ Finset.Icc 1 R},
          (allocationPrimeRowLoad infiniteAllocation ell r.1 : ℝ)) =
        (prefixAllocationPrimeLoad R ell : ℝ) := by
    exact_mod_cast sum_allocationPrimeRowLoad_subtype_eq_prefix R ell
  rw [hmass] at hrows
  apply hrows.congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp only
    rw [stationaryPrefixCofactorProductUpTo_factorization,
      Nat.cast_sum, Finset.sum_div]

/-- The certified capacity gives an eventual real bound for the
factorization of the actual cofactor product. -/
theorem eventually_stationaryPrefixCofactorProductUpTo_factorization_le_real
    (R : ℕ) {ell : ℕ} (hellPrime : ell.Prime)
    {slack : ℝ} (hslack : 0 < slack)
    (parts :
      ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ)
    (hparts :
      ∀ r : {r // r ∈ Finset.Icc 1 R},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      (((stationaryPrefixCofactorProductUpTo R
        (parts n)).factorization ell : ℕ) : ℝ) ≤
        ((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
          secondOrderScale n := by
  have htendsto :=
    stationaryPrefixCofactorProductUpTo_factorization_normalized_tendsto
      R ell parts hparts
  have hdenominatorNat : 0 < ell - 1 := by
    have := hellPrime.two_le
    omega
  have hdenominator : 0 < (((ell - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hdenominatorNat
  have hcapacity :
      (prefixAllocationPrimeLoad R ell : ℝ) ≤
        C0 / (((ell - 1 : ℕ) : ℝ)) := by
    rw [C0_eq_ratCast_C0Rat]
    exact_mod_cast prefixAllocationPrimeLoad_le_capacity R hellPrime
  have hstrict :
      (prefixAllocationPrimeLoad R ell : ℝ) <
        (C0 + slack) / (((ell - 1 : ℕ) : ℝ)) := by
    refine hcapacity.trans_lt ?_
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right
      (lt_add_of_pos_right C0 hslack) (inv_pos.mpr hdenominator)
  have hnormalized :=
    htendsto.eventually (eventually_lt_nhds hstrict)
  filter_upwards [hnormalized, eventually_secondOrderScale_pos] with n
    hn hscale
  exact ((div_lt_iff₀ hscale).mp hn).le

/-- Natural-number floor form of the same actual-product capacity bound. -/
theorem eventually_stationaryPrefixCofactorProductUpTo_factorization_le_nat
    (R : ℕ) {ell : ℕ} (hellPrime : ell.Prime)
    {slack : ℝ} (hslack : 0 < slack)
    (parts :
      ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ)
    (hparts :
      ∀ r : {r // r ∈ Finset.Icc 1 R},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      (stationaryPrefixCofactorProductUpTo R
        (parts n)).factorization ell ≤
        ⌊((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
          secondOrderScale n⌋₊ := by
  filter_upwards [
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_real
      R hellPrime hslack parts hparts] with n hn
  exact Nat.le_floor hn

/-- The actual cofactor-product capacity bounds hold simultaneously for
every fixed prime in the complete cofactor range through row R. -/
theorem
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_on_primesUpTo
    (R : ℕ) {slack : ℝ} (hslack : 0 < slack)
    (parts :
      ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ)
    (hparts :
      ∀ r : {r // r ∈ Finset.Icc 1 R},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ ell ∈ primesUpTo (2 * R + 1),
        ((((stationaryPrefixCofactorProductUpTo R
          (parts n)).factorization ell : ℕ) : ℝ) ≤
            ((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
              secondOrderScale n) ∧
          ((stationaryPrefixCofactorProductUpTo R
            (parts n)).factorization ell ≤
              ⌊((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
                secondOrderScale n⌋₊) := by
  rw [Finset.eventually_all]
  intro ell hell
  have hellPrime := (mem_primesUpTo.mp hell).1
  filter_upwards [
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_real
      R hellPrime hslack parts hparts,
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_nat
      R hellPrime hslack parts hparts] with n hreal hnat
  exact ⟨hreal, hnat⟩



end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.StationaryPrefixCentralCofactorChoice -/
section


/-!
# Actual fixed-prefix cofactor routing at the central-anchor cutoff

An exhaustive family of stationary-row partitions determines a literal
cofactor for every large central prime.  Row-zero primes receive cofactor
one.  A prime in a positive fixed row receives the unique label of the
partition part containing it.  This file proves that the resulting total
function is an admissible large-central cofactor choice and that its honest
large-cofactor product is exactly the previously analyzed fixed-prefix
product.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section





/-- The full realization certificate supplies the smaller routing API. -/
theorem isStationaryPrefixPartFamily_of_realization
    {R n : ℕ} {distinguished : ℕ → ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts :
      ∀ r : StationaryPrefixRow R,
        (∀ q ∈ infiniteAllocationPositiveSupport r.1,
          parts r q ⊆ stationaryPrimeLayer n r.1) ∧
        (∀ q ∈ infiniteAllocationPositiveSupport r.1,
          (parts r q).card =
            stationaryPrefixCount n r.1 (distinguished r.1) q) ∧
        (infiniteAllocationPositiveSupport r.1 : Set ℕ).PairwiseDisjoint
          (parts r) ∧
        (infiniteAllocationPositiveSupport r.1).biUnion (parts r) =
          stationaryPrimeLayer n r.1) :
    IsStationaryPrefixPartFamily R n parts := by
  intro r
  exact ⟨(hparts r).1, (hparts r).2.2.1, (hparts r).2.2.2⟩



theorem stationaryPrefixCofactorChoice_eq_one_of_rowZero
    {R n : ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    {p : ℕ} (hp : n < p) :
    stationaryPrefixCofactorChoice R n parts p = 1 := by
  simp only [stationaryPrefixCofactorChoice, if_pos hp]

/-- In a positive row, the choice really belongs to the selected part. -/
theorem stationaryPrefixCofactorChoice_spec
    {R n : ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    {p : ℕ} (hp : ¬n < p)
    (hrow : n / p ∈ Finset.Icc 1 R)
    (hmem :
      ∃ q ∈ infiniteAllocationPositiveSupport (n / p),
        p ∈ parts ⟨n / p, hrow⟩ q) :
    stationaryPrefixCofactorChoice R n parts p ∈
        infiniteAllocationPositiveSupport (n / p) ∧
      p ∈ parts ⟨n / p, hrow⟩
        (stationaryPrefixCofactorChoice R n parts p) := by
  rw [stationaryPrefixCofactorChoice, if_neg hp,
    dif_pos hrow, dif_pos hmem]
  exact Classical.choose_spec hmem

/-- Pairwise disjointness makes the cofactor attached to a marker in a
specified part equal to that part's label. -/
theorem stationaryPrefixCofactorChoice_eq_of_mem_part
    {R n : ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts)
    {r : StationaryPrefixRow R} {q p : ℕ}
    (hq : q ∈ infiniteAllocationPositiveSupport r.1)
    (hp : p ∈ parts r q) :
    stationaryPrefixCofactorChoice R n parts p = q := by
  have hpLayer : p ∈ stationaryPrimeLayer n r.1 :=
    (hparts r).1 q hq hp
  have hfloor := stationaryPrimeLayer_floor_values hpLayer
  have hrPos : 1 ≤ r.1 := (Finset.mem_Icc.mp r.2).1
  have hnotRowZero : ¬n < p := by
    intro hnp
    have hzero : n / p = 0 := Nat.div_eq_of_lt hnp
    omega
  have hrow : n / p ∈ Finset.Icc 1 R := by
    simpa only [hfloor.1] using r.2
  let row' : StationaryPrefixRow R := ⟨n / p, hrow⟩
  have hrowEq : row' = r := by
    apply Subtype.ext
    exact hfloor.1
  have hqRow' :
      q ∈ infiniteAllocationPositiveSupport (n / p) := by
    simpa only [hfloor.1] using hq
  have hpRow' : p ∈ parts row' q := by
    simpa only [hrowEq] using hp
  have hmem :
      ∃ q' ∈ infiniteAllocationPositiveSupport (n / p),
        p ∈ parts row' q' :=
    ⟨q, hqRow', hpRow'⟩
  have hchosen := stationaryPrefixCofactorChoice_spec
    hnotRowZero hrow hmem
  exact (hparts row').2.1.elim_finset
    hchosen.1 hqRow' p hchosen.2 hpRow'





/-- The nested marked-triple product is definitionally the row-by-row
cofactor product. -/
theorem stationaryPrefixMarkedTriples_prod_cofactor
    (R : ℕ)
    (parts : StationaryPrefixRow R → ℕ → Finset ℕ) :
    (stationaryPrefixMarkedTriples R parts).prod
        (fun x ↦ x.2.1) =
      stationaryPrefixCofactorProductUpTo R parts := by
  rw [stationaryPrefixMarkedTriples, Finset.prod_sigma]
  simp only [stationaryPrefixCofactorProductUpTo,
    stationaryPrefixCofactorProduct]

/-- Every marked triple yields a positive-row large central prime. -/
theorem stationaryPrefixMarkedTriple_marker_mem_largeCentralPrimes
    {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts)
    {x : Σ _r : StationaryPrefixRow R, Σ _q : ℕ, ℕ}
    (hx : x ∈ stationaryPrefixMarkedTriples R parts) :
    x.2.2 ∈
      (largeCentralPrimes n (centralAnchorCutoff R n)).filter
        (fun p ↦ p ≤ n) := by
  have hxmem := mem_stationaryPrefixMarkedTriples.mp hx
  have hpLayer : x.2.2 ∈ stationaryPrimeLayer n x.1.1 :=
    (hparts x.1).1 x.2.1 hxmem.1 hxmem.2
  have hpPrime := (mem_stationaryPrimeLayer.mp hpLayer).1
  have hrUpper : x.1.1 ≤ R := (Finset.mem_Icc.mp x.1.2).2
  have hpCutoff : centralAnchorCutoff R n < x.2.2 := by
    by_contra hnot
    have hpLe : x.2.2 ≤ centralAnchorCutoff R n :=
      Nat.le_of_not_gt hnot
    have hproduct : x.2.2 * (x.1.1 + 1) ≤ n := by
      calc
        x.2.2 * (x.1.1 + 1) ≤
            centralAnchorCutoff R n * (x.1.1 + 1) :=
          Nat.mul_le_mul_right (x.1.1 + 1) hpLe
        _ ≤ centralAnchorCutoff R n * (R + 1) :=
          Nat.mul_le_mul_left (centralAnchorCutoff R n)
            (Nat.succ_le_succ hrUpper)
        _ ≤ n := by
          simpa only [centralAnchorCutoff] using
            Nat.div_mul_le_self n (R + 1)
    exact (Nat.not_lt_of_ge hproduct)
      (mem_stationaryPrimeLayer.mp hpLayer).2.1
  have hpSq : 2 * n < x.2.2 ^ 2 :=
    (two_mul_lt_centralAnchorCutoff_sq hn).trans
      (Nat.pow_lt_pow_left hpCutoff (by decide : 2 ≠ 0))
  have hnPos : 0 < n :=
    (centralAnchorCutoffThreshold_pos R).trans_le hn
  have hpFactorization :
      (Nat.choose (2 * n) n).factorization x.2.2 = 1 :=
    centralChoose_factorization_eq_one_of_mem_stationaryPrimeLayer_of_sq
      hnPos hpLayer hpSq
  have hchooseNe : Nat.choose (2 * n) n ≠ 0 :=
    (Nat.choose_pos (by omega)).ne'
  have hpDvd : x.2.2 ∣ Nat.choose (2 * n) n :=
    (hpPrime.dvd_iff_one_le_factorization hchooseNe).mpr (by
      rw [hpFactorization])
  have hpFactors : x.2.2 ∈ (Nat.choose (2 * n) n).primeFactors :=
    hpPrime.mem_primeFactors hpDvd hchooseNe
  have hpLarge :
      x.2.2 ∈ largeCentralPrimes n (centralAnchorCutoff R n) := by
    exact Finset.mem_filter.mpr ⟨hpFactors, hpCutoff⟩
  have hpLeN : x.2.2 ≤ n := by
    by_contra hnot
    have hnp : n < x.2.2 := Nat.lt_of_not_ge hnot
    have hzero : n / x.2.2 = 0 := Nat.div_eq_of_lt hnp
    have hfloor := stationaryPrimeLayer_floor_values hpLayer
    have hrPos : 1 ≤ x.1.1 := (Finset.mem_Icc.mp x.1.2).1
    omega
  exact Finset.mem_filter.mpr ⟨hpLarge, hpLeN⟩

/-- Marker primes determine their row, and pairwise disjointness then
determines their cofactor label. -/
theorem stationaryPrefixMarkedTriple_marker_injOn
    {R n : ℕ}
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts) :
    Set.InjOn
      (fun x : Σ _r : StationaryPrefixRow R, Σ _q : ℕ, ℕ ↦ x.2.2)
      (stationaryPrefixMarkedTriples R parts) := by
  rintro ⟨rx, ⟨qx, px⟩⟩ hx ⟨ry, ⟨qy, py⟩⟩ hy hmarker
  have hxmem := mem_stationaryPrefixMarkedTriples.mp hx
  have hymem := mem_stationaryPrefixMarkedTriples.mp hy
  have hxLayer : px ∈ stationaryPrimeLayer n rx.1 :=
    (hparts rx).1 qx hxmem.1 hxmem.2
  have hyLayer : py ∈ stationaryPrimeLayer n ry.1 :=
    (hparts ry).1 qy hymem.1 hymem.2
  change px = py at hmarker
  have hrEq : rx = ry := by
    apply Subtype.ext
    rw [← (stationaryPrimeLayer_floor_values hxLayer).1,
      ← (stationaryPrimeLayer_floor_values hyLayer).1, hmarker]
  subst ry
  subst py
  have hqEq : qx = qy :=
    (hparts rx).2.1.elim_finset
      hxmem.1 hymem.1 px hxmem.2 hymem.2
  subst qy
  rfl

/-- Conversely, every positive-row large central prime occurs in exactly
one marked triple. -/
theorem exists_stationaryPrefixMarkedTriple_of_mem_largeCentralPrimes
    {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts)
    {p : ℕ}
    (hp : p ∈
      (largeCentralPrimes n (centralAnchorCutoff R n)).filter
        (fun marker ↦ marker ≤ n)) :
    ∃ x ∈ stationaryPrefixMarkedTriples R parts, x.2.2 = p := by
  have hpFilter := Finset.mem_filter.mp hp
  have hroute := largeCentralPrime_rowZero_or_fixedPrefix hn hpFilter.1
  rcases hroute.2 with hzero |
      ⟨r, hrPos, hrUpper, _hr, hpLayer⟩
  · omega
  · let row : StationaryPrefixRow R :=
      ⟨r, Finset.mem_Icc.mpr ⟨hrPos, hrUpper⟩⟩
    have hpUnion :
        p ∈ (infiniteAllocationPositiveSupport row.1).biUnion
          (parts row) := by
      rw [(hparts row).2.2]
      simpa only [row] using hpLayer
    obtain ⟨q, hq, hpPart⟩ := Finset.mem_biUnion.mp hpUnion
    refine ⟨⟨row, ⟨q, p⟩⟩, ?_, rfl⟩
    exact mem_stationaryPrefixMarkedTriples.mpr ⟨hq, hpPart⟩

/-- The realized total function follows the complete row-zero/fixed-prefix
routing specification. -/
theorem stationaryPrefixCofactorChoice_isLargeCentralCofactorChoice
    {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts) :
    IsLargeCentralCofactorChoice n (centralAnchorCutoff R n)
      (stationaryPrefixCofactorChoice R n parts) := by
  intro p hp
  have hroute := largeCentralPrime_rowZero_or_fixedPrefix hn hp
  rcases hroute.2 with hzero |
      ⟨r, hrPos, hrUpper, hr, hpLayer⟩
  · exact Or.inl ⟨hzero.1, hzero.2,
      stationaryPrefixCofactorChoice_eq_one_of_rowZero hzero.1⟩
  · have hnotRowZero : ¬n < p := by
      intro hnp
      have hzero : n / p = 0 := Nat.div_eq_of_lt hnp
      omega
    have hrow : n / p ∈ Finset.Icc 1 R := by
      rw [← hr]
      exact Finset.mem_Icc.mpr ⟨hrPos, hrUpper⟩
    let row : StationaryPrefixRow R := ⟨n / p, hrow⟩
    have hpUnion :
        p ∈ (infiniteAllocationPositiveSupport row.1).biUnion
          (parts row) := by
      rw [(hparts row).2.2]
      simpa only [row, hr] using hpLayer
    obtain ⟨q, hq, hpPart⟩ := Finset.mem_biUnion.mp hpUnion
    have hmem :
        ∃ q' ∈ infiniteAllocationPositiveSupport (n / p),
          p ∈ parts ⟨n / p, hrow⟩ q' :=
      ⟨q, hq, hpPart⟩
    have hchosen := stationaryPrefixCofactorChoice_spec
      hnotRowZero hrow hmem
    have hqRange := Finset.mem_Icc.mp
      (mem_infiniteAllocationPositiveSupport.mp hchosen.1).1
    have hqLower :
        r + 1 ≤ stationaryPrefixCofactorChoice R n parts p := by
      simpa only [hr] using hqRange.1
    have hqUpper :
        stationaryPrefixCofactorChoice R n parts p ≤ 2 * r + 1 := by
      simpa only [hr] using hqRange.2
    exact Or.inr ⟨r, hrPos, hr, hpLayer, hqLower, hqUpper⟩

/-- Literal factorization of an admissible large-cofactor product.  This
is the bridge from the product-valued capacity theorem to the explicit
finite sum expected by the reserve algebra. -/
theorem largeCentralCofactorProduct_factorization_eq_sum
    {n X ell : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    (largeCentralCofactorProduct n X q).factorization ell =
      ∑ p ∈ largeCentralPrimes n X, (q p).factorization ell := by
  rw [largeCentralCofactorProduct, Nat.factorization_prod_apply]
  intro p hp
  exact (largeCentralCofactor_pos hq hp).ne'

/-- The cofactor product of the routed total function is exactly the
row-by-row actual product whose valuation was analyzed previously. -/
theorem largeCentralCofactorProduct_stationaryPrefixCofactorChoice
    {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts) :
    largeCentralCofactorProduct n (centralAnchorCutoff R n)
        (stationaryPrefixCofactorChoice R n parts) =
      stationaryPrefixCofactorProductUpTo R parts := by
  let large := largeCentralPrimes n (centralAnchorCutoff R n)
  let positive := large.filter (fun p ↦ p ≤ n)
  have hrestrict :
      positive.prod (stationaryPrefixCofactorChoice R n parts) =
        large.prod (stationaryPrefixCofactorChoice R n parts) := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hpLarge hpNotPositive
    have hnotLe : ¬p ≤ n := by
      intro hpLe
      exact hpNotPositive (Finset.mem_filter.mpr ⟨hpLarge, hpLe⟩)
    exact stationaryPrefixCofactorChoice_eq_one_of_rowZero
      (Nat.lt_of_not_ge hnotLe)
  have hbij :
      (stationaryPrefixMarkedTriples R parts).prod
          (fun x ↦ x.2.1) =
        positive.prod (stationaryPrefixCofactorChoice R n parts) := by
    apply Finset.prod_bij (fun x _hx ↦ x.2.2)
    · intro x hx
      simpa only [positive, large] using
        stationaryPrefixMarkedTriple_marker_mem_largeCentralPrimes
          hn hparts hx
    · intro x hx y hy hxy
      exact stationaryPrefixMarkedTriple_marker_injOn hparts hx hy hxy
    · intro p hp
      have hp' :
          p ∈ (largeCentralPrimes n (centralAnchorCutoff R n)).filter
            (fun marker ↦ marker ≤ n) := by
        simpa only [positive, large] using hp
      obtain ⟨x, hx, hmarker⟩ :=
        exists_stationaryPrefixMarkedTriple_of_mem_largeCentralPrimes
          hn hparts hp'
      exact ⟨x, hx, hmarker⟩
    · intro x hx
      have hxmem := mem_stationaryPrefixMarkedTriples.mp hx
      exact (stationaryPrefixCofactorChoice_eq_of_mem_part
        hparts hxmem.1 hxmem.2).symm
  calc
    largeCentralCofactorProduct n (centralAnchorCutoff R n)
        (stationaryPrefixCofactorChoice R n parts) =
        large.prod (stationaryPrefixCofactorChoice R n parts) := by
      rfl
    _ = positive.prod (stationaryPrefixCofactorChoice R n parts) :=
      hrestrict.symm
    _ = (stationaryPrefixMarkedTriples R parts).prod
        (fun x ↦ x.2.1) := hbij.symm
    _ = stationaryPrefixCofactorProductUpTo R parts :=
      stationaryPrefixMarkedTriples_prod_cofactor R parts

/-- The existing complete central-anchor product theorem now applies to
the actual realized prefix cofactors, with no abstract choice remaining. -/
theorem fullCentralAnchors_prod_stationaryPrefixCofactorChoice
    {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts) :
    (fullCentralAnchors n (centralAnchorCutoff R n)
        (stationaryPrefixCofactorChoice R n parts)).prod id =
      Nat.choose (2 * n) n *
        (2 ^ residualPromotionCost n (centralAnchorCutoff R n) *
          stationaryPrefixCofactorProductUpTo R parts) := by
  have hchoice :=
    stationaryPrefixCofactorChoice_isLargeCentralCofactorChoice hn hparts
  calc
    (fullCentralAnchors n (centralAnchorCutoff R n)
        (stationaryPrefixCofactorChoice R n parts)).prod id =
        Nat.choose (2 * n) n *
          centralAnchorDivisor n (centralAnchorCutoff R n)
            (stationaryPrefixCofactorChoice R n parts) :=
      fullCentralAnchors_prod_centralAnchorCutoff hn hchoice
    _ = Nat.choose (2 * n) n *
        (2 ^ residualPromotionCost n (centralAnchorCutoff R n) *
          stationaryPrefixCofactorProductUpTo R parts) := by
      rw [centralAnchorDivisor,
        largeCentralCofactorProduct_stationaryPrefixCofactorChoice
          hn hparts]

/-- For any simultaneous realization, admissibility and the exact product
identification both hold eventually. -/
theorem eventually_stationaryPrefixCofactorChoice_certificate
    (R : ℕ) (distinguished : ℕ → ℕ)
    (parts : ℕ → StationaryPrefixRow R → ℕ → Finset ℕ)
    (hparts :
      ∀ᶠ n : ℕ in atTop,
        ∀ r : StationaryPrefixRow R,
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            parts n r q ⊆ stationaryPrimeLayer n r.1) ∧
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            (parts n r q).card =
              stationaryPrefixCount n r.1 (distinguished r.1) q) ∧
          (infiniteAllocationPositiveSupport r.1 :
            Set ℕ).PairwiseDisjoint (parts n r) ∧
          (infiniteAllocationPositiveSupport r.1).biUnion
              (parts n r) = stationaryPrimeLayer n r.1) :
    ∀ᶠ n : ℕ in atTop,
      IsLargeCentralCofactorChoice n (centralAnchorCutoff R n)
          (stationaryPrefixCofactorChoice R n (parts n)) ∧
        largeCentralCofactorProduct n (centralAnchorCutoff R n)
            (stationaryPrefixCofactorChoice R n (parts n)) =
          stationaryPrefixCofactorProductUpTo R (parts n) ∧
        (fullCentralAnchors n (centralAnchorCutoff R n)
            (stationaryPrefixCofactorChoice R n (parts n))).prod id =
          Nat.choose (2 * n) n *
            (2 ^ residualPromotionCost n (centralAnchorCutoff R n) *
              stationaryPrefixCofactorProductUpTo R (parts n)) := by
  filter_upwards [hparts,
    eventually_ge_atTop (centralAnchorCutoffThreshold R)] with n
    hpartsN hn
  have hfamily :=
    isStationaryPrefixPartFamily_of_realization hpartsN
  exact ⟨stationaryPrefixCofactorChoice_isLargeCentralCofactorChoice
      hn hfamily,
    largeCentralCofactorProduct_stationaryPrefixCofactorChoice hn hfamily,
    fullCentralAnchors_prod_stationaryPrefixCofactorChoice hn hfamily⟩

/-- The capacity estimate is therefore a simultaneous estimate for the
literal routed large-central cofactor product, for every prime that can
occur in a prefix cofactor through row `R`. -/
theorem
    eventually_stationaryPrefixCofactorChoice_factorization_le_on_primesUpTo
    (R : ℕ) (distinguished : ℕ → ℕ)
    {slack : ℝ} (hslack : 0 < slack)
    (parts : ℕ → StationaryPrefixRow R → ℕ → Finset ℕ)
    (hactual :
      ∀ᶠ n : ℕ in atTop,
        ∀ r : StationaryPrefixRow R,
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            parts n r q ⊆ stationaryPrimeLayer n r.1) ∧
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            (parts n r q).card =
              stationaryPrefixCount n r.1 (distinguished r.1) q) ∧
          (infiniteAllocationPositiveSupport r.1 :
            Set ℕ).PairwiseDisjoint (parts n r) ∧
          (infiniteAllocationPositiveSupport r.1).biUnion
              (parts n r) = stationaryPrimeLayer n r.1)
    (hparts :
      ∀ r : StationaryPrefixRow R,
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ ell ∈ primesUpTo (2 * R + 1),
        ((((largeCentralCofactorProduct n (centralAnchorCutoff R n)
          (stationaryPrefixCofactorChoice R n
            (parts n))).factorization ell : ℕ) : ℝ) ≤
            ((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
              secondOrderScale n) ∧
          ((largeCentralCofactorProduct n (centralAnchorCutoff R n)
            (stationaryPrefixCofactorChoice R n
              (parts n))).factorization ell ≤
                ⌊((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
                  secondOrderScale n⌋₊) := by
  filter_upwards [
    eventually_stationaryPrefixCofactorChoice_certificate
      R distinguished parts hactual,
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_on_primesUpTo
      R hslack parts hparts] with n hcertificate hcapacity
  intro ell hell
  simpa only [hcertificate.2.1] using hcapacity ell hell

end

end Erdos390.WholePaper

end

/- Source module: Erdos390.WholePaper.CentralAnchorExistence -/
section


/-!
# Eventual existence of the complete central-anchor family

For every `c > C0`, one fixed prefix depth is chosen.  The promotion cost,
actual stationary-prefix allocation, and factorial-tail reserve are then
combined into an honest routed cofactor function and an honest finite set
of central anchors.  The certificate records interval containment, the
exact product identity, and literal divisibility of the anchor divisor into
the upper tail product.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section



theorem stationaryPrefixDistinguished_mem
    {r : ℕ} (hr : 1 ≤ r) :
    stationaryPrefixDistinguished r ∈
      infiniteAllocationPositiveSupport r := by
  rw [stationaryPrefixDistinguished, dif_pos hr]
  exact Classical.choose_spec
    (infiniteAllocationPositiveSupport_nonempty r hr)



/-- Terminal central-anchor existence theorem.  The prefix depth (and hence
the finite support) is fixed before `n`; all remaining data and every
quantitative reserve inequality are actual finite statements at that `n`. -/
theorem exists_eventually_centralAnchorCertificate
    {c : ℝ} (hc : C0 < c) :
    ∃ R : ℕ, 201 ≤ R ∧
      ∀ᶠ n : ℕ in atTop,
        Nonempty (CentralAnchorCertificate c R n) := by
  let epsilon : ℝ := c - C0
  have hepsilon : 0 < epsilon := by
    simpa only [epsilon] using sub_pos.mpr hc
  have hcEq : c = C0 + epsilon := by
    simp only [epsilon]
    ring
  have hC0Pos : (0 : ℝ) < C0 := by
    norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hpromotionTolerance : 0 < epsilon / 4 := by
    positivity
  obtain ⟨R, hR, hpromotion⟩ :=
    residualPromotionCost_eventually_cast_le_mul
      hpromotionTolerance
  let distinguished : ℕ → ℕ := stationaryPrefixDistinguished
  have hdistinguished :
      ∀ r ∈ Finset.Icc 1 R,
        distinguished r ∈ infiniteAllocationPositiveSupport r := by
    intro r hr
    exact stationaryPrefixDistinguished_mem
      (Finset.mem_Icc.mp hr).1
  obtain ⟨parts, hactual, hparts⟩ :=
    exists_stationaryPrefixParts_on_finset
      (Finset.Icc 1 R)
      (fun r hr ↦ (Finset.mem_Icc.mp hr).1)
      distinguished hdistinguished
  have hrouted :=
    eventually_stationaryPrefixCofactorChoice_certificate
      R distinguished parts hactual
  have hcofactor :=
    eventually_stationaryPrefixCofactorChoice_factorization_le_on_primesUpTo
      R distinguished (show 0 < epsilon / 6 by positivity)
      parts hactual hparts
  have htailReserve :
      ∀ᶠ n : ℕ in atTop,
        ∀ ell ∈ primesUpTo (2 * R + 1),
          (c / (((ell - 1 : ℕ) : ℝ)) -
              epsilon / (6 * (((ell - 1 : ℕ) : ℝ)))) *
              secondOrderScale n ≤
            (upperTailValuation c n ell : ℝ) := by
    apply eventually_upperTailValuation_ge_mul_scale_on_finset
      hcPos (primesUpTo (2 * R + 1))
      (fun ell ↦
        c / (((ell - 1 : ℕ) : ℝ)) -
          epsilon / (6 * (((ell - 1 : ℕ) : ℝ))))
    · intro ell hell
      exact (mem_primesUpTo.mp hell).1
    · intro ell hell
      have hellPrime := (mem_primesUpTo.mp hell).1
      have hdenominator : 0 < (((ell - 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.sub_pos_of_lt hellPrime.one_lt
      have hreservePos :
          0 < epsilon /
            (6 * (((ell - 1 : ℕ) : ℝ))) :=
        div_pos hepsilon (mul_pos (by norm_num) hdenominator)
      exact sub_lt_self _ hreservePos
  have hmax : max 2 (2 * R + 1) = 2 * R + 1 := by
    omega
  refine ⟨R, hR, ?_⟩
  filter_upwards [hrouted, hcofactor, hpromotion, htailReserve,
    eventually_secondOrderScale_pos,
    eventually_ge_atTop (centralAnchorCutoffThreshold R)] with n
    hroutedN hcofactorN hpromotionN htailN hscale hnCutoff
  let q : ℕ → ℕ :=
    stationaryPrefixCofactorChoice R n (parts n)
  have hqChoice :
      IsLargeCentralCofactorChoice n (centralAnchorCutoff R n) q := by
    simpa only [q] using hroutedN.1
  have hqBound :
      ∀ p ∈ largeCentralPrimes n (centralAnchorCutoff R n),
        q p ≤ 2 * R + 1 := by
    intro p hp
    exact largeCentralCofactor_le_fixedPrefix hqChoice hp
  have hcofactorSum :
      ∀ ell ∈ primesUpTo (max 2 (2 * R + 1)),
        ((∑ p ∈ largeCentralPrimes n (centralAnchorCutoff R n),
            (q p).factorization ell : ℕ) : ℝ) ≤
          (C0 / (((ell - 1 : ℕ) : ℝ)) +
              epsilon /
                (6 * (((ell - 1 : ℕ) : ℝ)))) *
            secondOrderScale n := by
    intro ell hell
    have hellPrefix : ell ∈ primesUpTo (2 * R + 1) := by
      simpa only [hmax] using hell
    have hproductBound := (hcofactorN ell hellPrefix).1
    have hfactorization :=
      largeCentralCofactorProduct_factorization_eq_sum
        (ell := ell) hqChoice
    rw [← hfactorization]
    calc
      (((largeCentralCofactorProduct n (centralAnchorCutoff R n)
          q).factorization ell : ℕ) : ℝ) ≤
          ((C0 + epsilon / 6) /
              (((ell - 1 : ℕ) : ℝ))) *
            secondOrderScale n := by
        simpa only [q] using hproductBound
      _ = (C0 / (((ell - 1 : ℕ) : ℝ)) +
              epsilon /
                (6 * (((ell - 1 : ℕ) : ℝ)))) *
            secondOrderScale n := by
        ring
  have hpromotionCutoff :
      (residualPromotionCost n (centralAnchorCutoff R n) : ℝ) ≤
        epsilon / 4 * secondOrderScale n := by
    simpa only [centralAnchorCutoff] using hpromotionN
  have htail :
      ∀ ell ∈ primesUpTo (max 2 (2 * R + 1)),
        (c / (((ell - 1 : ℕ) : ℝ)) -
            epsilon /
              (6 * (((ell - 1 : ℕ) : ℝ)))) *
            secondOrderScale n ≤
          (upperTailValuation c n ell : ℝ) := by
    intro ell hell
    exact htailN ell (by simpa only [hmax] using hell)
  have hdivisor :
      centralAnchorDivisor n (centralAnchorCutoff R n) q ∣
        centralTailProduct n (upperTailLength c n) := by
    exact centralAnchorDivisor_dvd_upperTail_of_slack
      (c := c) (epsilon := epsilon) (scale := secondOrderScale n)
      (n := n) (X := centralAnchorCutoff R n) (B := 2 * R + 1)
      (q := q) hcEq hepsilon hscale.le hqChoice hqBound
      hcofactorSum hpromotionCutoff htail
  have hdivisorSupport :
      ∀ ℓ : ℕ, ℓ.Prime →
        ℓ ∣ centralAnchorDivisor n (centralAnchorCutoff R n) q →
          ℓ ∈ primesUpTo (2 * R + 1) := by
    intro ℓ hℓPrime hℓDivisor
    apply mem_primesUpTo.mpr
    refine ⟨hℓPrime, ?_⟩
    have hbound := prime_dvd_centralAnchorDivisor_le hqChoice hqBound
      hℓPrime hℓDivisor
    simpa only [hmax] using hbound
  have hdivisorReserve :
      ∀ ℓ ∈ primesUpTo (2 * R + 1),
        (c - C0) / (3 * (((ℓ - 1 : ℕ) : ℝ))) *
              secondOrderScale n +
            ((centralAnchorDivisor n
              (centralAnchorCutoff R n) q).factorization ℓ : ℝ) ≤
          (upperTailValuation c n ℓ : ℝ) := by
    intro ℓ hℓ
    have hℓMax : ℓ ∈ primesUpTo (max 2 (2 * R + 1)) := by
      simpa only [hmax] using hℓ
    have hreserve :=
      centralAnchorDivisor_factorization_add_reserve_le_upperTailValuation_of_slack
        (c := c) (epsilon := epsilon) (scale := secondOrderScale n)
        (n := n) (X := centralAnchorCutoff R n) (ℓ := ℓ) (q := q)
        hcEq hepsilon hscale.le (mem_primesUpTo.mp hℓ).1 hqChoice
        (hcofactorSum ℓ hℓMax) hpromotionCutoff (htail ℓ hℓMax)
    have hepsilonEq : c - C0 = epsilon := by
      rw [hcEq]
      ring
    simpa only [hepsilonEq] using hreserve
  have hnPos : 0 < n :=
    (centralAnchorCutoffThreshold_pos R).trans_le hnCutoff
  let anchors : Finset ℕ :=
    fullCentralAnchors n (centralAnchorCutoff R n) q
  refine ⟨{
    q := q
    anchors := anchors
    isCofactorChoice := hqChoice
    anchors_eq := rfl
    anchors_subset := ?_
    anchors_prod := ?_
    divisor_prime_support := hdivisorSupport
    divisor_reserve := hdivisorReserve
    divisor_dvd_tail := hdivisor
  }⟩
  · simpa only [anchors] using
      fullCentralAnchors_subset_centralInterval hnPos hqChoice
  · simpa only [anchors] using
      fullCentralAnchors_prod_centralAnchorCutoff hnCutoff hqChoice

end

end Erdos390.WholePaper

end

theorem solution : Erdos390.RemainingAnalyticGoal008_012 := by
  exact @Erdos390.WholePaper.exists_eventually_centralAnchorCertificate
