-- Prove2me | solution 2 for RLHF.audit_gap_tendsto_cov
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T04:13:04.039983+00:00
-- url     : https://prove2.me/submissions/3762e178-69e8-4501-8285-c75c474a8296

import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation

open RLHF Finset Filter in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {r p : Ω → ℝ} (hp : IsPosDist p)
    (f : Ω → ℝ) :
    Filter.Tendsto (fun β : ℝ => β * (mean (gibbsPolicy β r p) f - mean p f)) Filter.atTop
      (nhds (cov p r f)) := by
  -- the audit gap is `O(1/β²)` once `β` exceeds the reward range
  have hb : ∀ β : ℝ, 0 < β → rewardRange r ≤ β →
      |mean (gibbsPolicy β r p) f - mean p f - cov p r f / β|
        ≤ 2 * (rewardRange f * (variance p r / β ^ 2)) := by
    intro β hβ hr
    obtain ⟨hpos, htot⟩ := hp
    set m := mean p r with hm
    set c : Ω → ℝ := fun y => (r y - m) / β with hcdef
    set Z := ∑ y, p y * Real.exp (c y) with hZdef
    set V := variance p r / β ^ 2 with hVdef
    set A := mad p r / β with hAdef
    -- the centred, rescaled reward stays in `[-1, 1]`
    have hsup : ∀ y, r y ≤ univ.sup' univ_nonempty r := fun y => le_sup' r (mem_univ y)
    have hinf : ∀ y, univ.inf' univ_nonempty r ≤ r y := fun y => inf'_le r (mem_univ y)
    have hmle : m ≤ univ.sup' univ_nonempty r := by
      calc m = ∑ y, p y * r y := rfl
        _ ≤ ∑ y, p y * univ.sup' univ_nonempty r :=
            sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hsup y) (hpos y).le
        _ = univ.sup' univ_nonempty r := by rw [← sum_mul, htot, one_mul]
    have hmge : univ.inf' univ_nonempty r ≤ m := by
      calc univ.inf' univ_nonempty r = ∑ y, p y * univ.inf' univ_nonempty r := by
            rw [← sum_mul, htot, one_mul]
        _ ≤ ∑ y, p y * r y :=
            sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hinf y) (hpos y).le
        _ = m := rfl
    have hc : ∀ y, |c y| ≤ 1 := by
      intro y
      have h1 : |r y - m| ≤ β := by
        rw [abs_le]
        have := hsup y
        have := hinf y
        unfold rewardRange at hr
        constructor <;> linarith
      show |(r y - m) / β| ≤ 1
      rw [abs_div, abs_of_pos hβ, div_le_one hβ]
      exact h1
    -- first and second moments of `c`
    have hEc : ∑ y, p y * c y = 0 := by
      have h1 : ∀ y, p y * c y = (p y * r y - m * p y) / β := by
        intro y
        simp only [hcdef]
        ring
      rw [sum_congr rfl fun y _ => h1 y, ← sum_div, sum_sub_distrib, ← mul_sum, htot]
      simp [hm, mean]
    have hsumV : ∑ y, p y * c y ^ 2 = V := by
      rw [hVdef, variance, sum_div]
      refine sum_congr rfl fun y _ => ?_
      simp only [hcdef]
      ring
    have hsumA : ∑ y, p y * |c y| = A := by
      rw [hAdef, mad, sum_div]
      refine sum_congr rfl fun y _ => ?_
      simp only [hcdef]
      rw [abs_div, abs_of_pos hβ]
      ring
    have hV0 : 0 ≤ V := by
      rw [← hsumV]
      exact sum_nonneg fun y _ => mul_nonneg (hpos y).le (sq_nonneg _)
    have hA1 : A ≤ 1 := by
      rw [← hsumA]
      calc ∑ y, p y * |c y| ≤ ∑ y, p y * 1 :=
            sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hc y) (hpos y).le
        _ = 1 := by rw [← sum_mul, htot, one_mul]
    -- the normaliser: `1 ≤ Z ≤ 1 + V`
    have hZ1 : 1 ≤ Z := by
      calc (1 : ℝ) = ∑ y, p y * (c y + 1) := by
            rw [sum_congr rfl fun y _ => mul_add (p y) (c y) 1, sum_add_distrib, hEc]
            simp [htot]
        _ ≤ Z := sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (Real.add_one_le_exp (c y)) (hpos y).le
    have hZ2 : Z ≤ 1 + V := by
      calc Z ≤ ∑ y, p y * (1 + c y + c y ^ 2) := sum_le_sum fun y _ => by
            have := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le (hc y))).2
            exact mul_le_mul_of_nonneg_left (by linarith) (hpos y).le
        _ = 1 + V := by
            simp only [mul_add, sum_add_distrib, hEc, hsumV, mul_one, htot]
            ring
    have hZpos : 0 < Z := by linarith
    have hZne : Z ≠ 0 := hZpos.ne'
    -- the Gibbs policy in centred form
    have hsplit : ∀ y, Real.exp (r y / β) = Real.exp (m / β) * Real.exp (c y) := by
      intro y
      rw [← Real.exp_add]
      congr 1
      simp only [hcdef]
      field_simp
      ring
    have hpart : partition β r p = Real.exp (m / β) * Z := by
      simp only [partition, hsplit, hZdef, mul_sum]
      exact sum_congr rfl fun y _ => by ring
    have hπ : ∀ y, gibbsPolicy β r p y = p y * Real.exp (c y) / Z := by
      intro y
      simp only [gibbsPolicy]
      rw [hpart, hsplit, mul_left_comm, mul_div_mul_left _ _ (Real.exp_pos _).ne']
    have hl1 : l1Dist (gibbsPolicy β r p) p = (∑ y, p y * |Real.exp (c y) - Z|) / Z := by
      rw [l1Dist, sum_div]
      refine sum_congr rfl fun y _ => ?_
      rw [hπ y]
      have h1 : p y * Real.exp (c y) / Z - p y = p y * (Real.exp (c y) - Z) / Z := by
        field_simp
      rw [h1, abs_div, abs_mul, abs_of_pos (hpos y), abs_of_pos hZpos]
    -- the audit gap, centred at `μ = 𝔼_p f`
    set μ := mean p f with hμ
    set g : Ω → ℝ := fun y => f y - μ with hgdef
    have hgR : ∀ y, |g y| ≤ rewardRange f := by
      intro y
      have hs : ∀ y, f y ≤ univ.sup' univ_nonempty f := fun y => le_sup' f (mem_univ y)
      have hi : ∀ y, univ.inf' univ_nonempty f ≤ f y := fun y => inf'_le f (mem_univ y)
      have hμle : μ ≤ univ.sup' univ_nonempty f := by
        calc μ = ∑ y, p y * f y := rfl
          _ ≤ ∑ y, p y * univ.sup' univ_nonempty f :=
              sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hs y) (hpos y).le
          _ = univ.sup' univ_nonempty f := by rw [← sum_mul, htot, one_mul]
      have hμge : univ.inf' univ_nonempty f ≤ μ := by
        calc univ.inf' univ_nonempty f = ∑ y, p y * univ.inf' univ_nonempty f := by
              rw [← sum_mul, htot, one_mul]
          _ ≤ ∑ y, p y * f y :=
              sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hi y) (hpos y).le
          _ = μ := rfl
      show |f y - μ| ≤ rewardRange f
      unfold rewardRange
      rw [abs_le]
      have := hs y
      have := hi y
      constructor <;> linarith
    have hR0 : 0 ≤ rewardRange f := (abs_nonneg _).trans (hgR (Classical.arbitrary Ω))
    have hsg : ∑ y, p y * g y = 0 := by
      simp only [hgdef, mul_sub, sum_sub_distrib, ← sum_mul, htot, one_mul]
      simp [hμ, mean]
    have hmeanπ : mean (gibbsPolicy β r p) f = (∑ y, p y * Real.exp (c y) * f y) / Z := by
      rw [mean, sum_div]
      exact sum_congr rfl fun y _ => by rw [hπ y]; ring
    have hcovβ : cov p r f / β = ∑ y, p y * c y * g y := by
      rw [cov, sum_div]
      refine sum_congr rfl fun y _ => ?_
      simp only [hcdef, hgdef]
      ring
    have hexpg : ∑ y, p y * Real.exp (c y) * g y
        = ∑ y, p y * Real.exp (c y) * f y - μ * Z := by
      simp only [hgdef, mul_sub, sum_sub_distrib, hZdef, mul_sum]
      congr 1
      exact sum_congr rfl fun y _ => by ring
    have hkey : (mean (gibbsPolicy β r p) f - μ - cov p r f / β) * Z
        = ∑ y, p y * ((Real.exp (c y) - 1 - c y) + (1 - Z) * c y) * g y := by
      have hsplitsum : ∑ y, p y * ((Real.exp (c y) - 1 - c y) + (1 - Z) * c y) * g y
          = ∑ y, p y * Real.exp (c y) * g y - ∑ y, p y * g y - ∑ y, p y * c y * g y
            + (1 - Z) * ∑ y, p y * c y * g y := by
        simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun y _ => by ring
      rw [hsplitsum, hexpg, hsg, ← hcovβ, hmeanπ]
      field_simp
      ring
    have hgap : |mean (gibbsPolicy β r p) f - μ - cov p r f / β|
        ≤ 2 * (rewardRange f * V) := by
      have hpt : ∀ y, |p y * ((Real.exp (c y) - 1 - c y) + (1 - Z) * c y) * g y|
          ≤ p y * (c y ^ 2 + (Z - 1)) * rewardRange f := by
        intro y
        have h1 := Real.abs_exp_sub_one_sub_id_le (hc y)
        have h2 : |(1 - Z) * c y| ≤ Z - 1 := by
          rw [abs_mul, abs_of_nonpos (by linarith : 1 - Z ≤ 0)]
          nlinarith [hc y, abs_nonneg (c y)]
        have h3 : |(Real.exp (c y) - 1 - c y) + (1 - Z) * c y| ≤ c y ^ 2 + (Z - 1) :=
          (abs_add_le _ _).trans (by linarith)
        rw [abs_mul, abs_mul, abs_of_pos (hpos y)]
        have h4 : 0 ≤ c y ^ 2 + (Z - 1) := by nlinarith [sq_nonneg (c y)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h3 (hpos y).le) (hgR y)
          (abs_nonneg _) (mul_nonneg (hpos y).le h4)
      have hsum : ∑ y, p y * (c y ^ 2 + (Z - 1)) * rewardRange f
          = (V + (Z - 1)) * rewardRange f := by
        rw [← sum_mul]
        congr 1
        simp only [mul_add, sum_add_distrib, hsumV, ← sum_mul, htot, one_mul]
      have hD : |(mean (gibbsPolicy β r p) f - μ - cov p r f / β) * Z|
          ≤ (V + (Z - 1)) * rewardRange f := by
        rw [hkey]
        exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun y _ => hpt y).trans hsum.le)
      rw [abs_mul, abs_of_pos hZpos] at hD
      nlinarith [mul_le_mul_of_nonneg_left hZ1
        (abs_nonneg (mean (gibbsPolicy β r p) f - μ - cov p r f / β)),
        mul_le_mul_of_nonneg_right hZ2 hR0]
    exact hgap
  have hlo : Tendsto (fun β : ℝ => cov p r f - 2 * rewardRange f * variance p r / β) atTop
      (nhds (cov p r f)) := by
    have h := (tendsto_const_nhds (x := 2 * rewardRange f * variance p r)).div_atTop tendsto_id
    simpa using (tendsto_const_nhds (x := cov p r f)).sub h
  have hhi : Tendsto (fun β : ℝ => cov p r f + 2 * rewardRange f * variance p r / β) atTop
      (nhds (cov p r f)) := by
    have h := (tendsto_const_nhds (x := 2 * rewardRange f * variance p r)).div_atTop tendsto_id
    simpa using (tendsto_const_nhds (x := cov p r f)).add h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop (max (rewardRange r) 1)] with β hβ
    have hβpos : 0 < β := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hβ)
    have h1 := (abs_le.1 (hb β hβpos (le_trans (le_max_left _ _) hβ))).1
    have h2 := mul_le_mul_of_nonneg_left h1 hβpos.le
    have e : β * (mean (gibbsPolicy β r p) f - mean p f)
        = β * (mean (gibbsPolicy β r p) f - mean p f - cov p r f / β) + cov p r f := by
      field_simp
      ring
    have e2 : β * -(2 * (rewardRange f * (variance p r / β ^ 2)))
        = -(2 * rewardRange f * variance p r / β) := by
      field_simp
    rw [e2] at h2
    rw [e]
    linarith
  · filter_upwards [eventually_ge_atTop (max (rewardRange r) 1)] with β hβ
    have hβpos : 0 < β := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hβ)
    have h1 := (abs_le.1 (hb β hβpos (le_trans (le_max_left _ _) hβ))).2
    have h2 := mul_le_mul_of_nonneg_left h1 hβpos.le
    have e : β * (mean (gibbsPolicy β r p) f - mean p f)
        = β * (mean (gibbsPolicy β r p) f - mean p f - cov p r f / β) + cov p r f := by
      field_simp
      ring
    have e2 : β * (2 * (rewardRange f * (variance p r / β ^ 2)))
        = 2 * rewardRange f * variance p r / β := by
      field_simp
    rw [e2] at h2
    rw [e]
    linarith
