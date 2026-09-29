-- Prove2me | solution 2 for RLHF.sqrt_two_kl_tendsto_stddev
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T05:42:55.846841+00:00
-- url     : https://prove2.me/submissions/af13f9ad-d2e2-4e23-9575-edebf777d161

import Mathlib
import Definitions.Def_Algebra_RLHFDriftCore
import Definitions.Def_Algebra_RLHFMeanAbsoluteDeviation

open RLHF Finset Filter in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {r p : Ω → ℝ} (hp : IsPosDist p) :
    Filter.Tendsto (fun β : ℝ => β * Real.sqrt (2 * klDiv (gibbsPolicy β r p) p))
      Filter.atTop (nhds (Real.sqrt (variance p r))) := by
  -- the quantitative bound `|KL − Var/(2β²)| = O(range·Var/β³ + Var²/β⁴)` for `β ≥ range`
  have hb : ∀ β : ℝ, 0 < β → rewardRange r ≤ β →
      |klDiv (gibbsPolicy β r p) p - variance p r / β ^ 2 / 2|
        ≤ 2 * (rewardRange r * variance p r / β ^ 3) + 3 * (variance p r ^ 2 / β ^ 4) := by
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
    -- finer control: `|c| ≤ ρ = range / β`
    set ρ := rewardRange r / β with hρdef
    have hρ0 : 0 ≤ ρ := by
      rw [hρdef]
      apply div_nonneg _ hβ.le
      unfold rewardRange
      linarith [hsup (Classical.arbitrary Ω), hinf (Classical.arbitrary Ω)]
    have hcρ : ∀ y, |c y| ≤ ρ := by
      intro y
      have h1 : |r y - m| ≤ rewardRange r := by
        rw [abs_le]
        have := hsup y
        have := hinf y
        unfold rewardRange
        constructor <;> linarith
      show |(r y - m) / β| ≤ ρ
      rw [abs_div, abs_of_pos hβ, hρdef]
      exact div_le_div_of_nonneg_right h1 hβ.le
    have hcube : ∀ y, |c y| ^ 3 ≤ ρ * c y ^ 2 := by
      intro y
      have h := hcρ y
      have h2 : c y ^ 2 = |c y| ^ 2 := (sq_abs _).symm
      rw [h2]
      have h3 : |c y| ^ 3 = |c y| * |c y| ^ 2 := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_right h (by positivity)
    -- third-order remainder of the exponential
    have hexp3 : ∀ y, |Real.exp (c y) - 1 - c y - c y ^ 2 / 2| ≤ |c y| ^ 3 := by
      intro y
      have h := Real.exp_bound (hc y) (by norm_num : 0 < 3)
      have hs : ∑ i ∈ Finset.range 3, c y ^ i / (i.factorial : ℝ) = 1 + c y + c y ^ 2 / 2 := by
        simp [Finset.sum_range_succ, Nat.factorial]
      rw [hs] at h
      have h2 : |Real.exp (c y) - 1 - c y - c y ^ 2 / 2|
          = |Real.exp (c y) - (1 + c y + c y ^ 2 / 2)| := by
        congr 1
        ring
      rw [h2]
      exact h.trans (mul_le_of_le_one_right (by positivity) (by norm_num [Nat.factorial]))
    set T := ∑ y, p y * c y * Real.exp (c y) with hTdef
    have hT : |T - V| ≤ ρ * V := by
      have e : T - V = ∑ y, p y * (c y * (Real.exp (c y) - 1 - c y)) := by
        rw [hTdef, ← hsumV]
        have h0 : ∑ y, p y * c y * 1 = 0 := by simpa using hEc
        rw [← sub_zero (∑ y, p y * c y * Real.exp (c y) - ∑ y, p y * c y ^ 2), ← h0]
        simp only [← sum_sub_distrib]
        exact sum_congr rfl fun y _ => by ring
      rw [e]
      calc |∑ y, p y * (c y * (Real.exp (c y) - 1 - c y))|
          ≤ ∑ y, |p y * (c y * (Real.exp (c y) - 1 - c y))| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ y, p y * (ρ * c y ^ 2) := by
            refine sum_le_sum fun y _ => ?_
            rw [abs_mul, abs_mul, abs_of_pos (hpos y)]
            have h1 := Real.abs_exp_sub_one_sub_id_le (hc y)
            have h2 : |c y| * |Real.exp (c y) - 1 - c y| ≤ |c y| * c y ^ 2 :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
            have h3 : |c y| * c y ^ 2 ≤ ρ * c y ^ 2 :=
              mul_le_mul_of_nonneg_right (hcρ y) (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left (h2.trans h3) (hpos y).le
        _ = ρ * V := by
            rw [← hsumV, mul_sum]
            exact sum_congr rfl fun y _ => by ring
    have hδ : |Z - 1 - V / 2| ≤ ρ * V := by
      have e : Z - 1 - V / 2 = ∑ y, p y * (Real.exp (c y) - 1 - c y - c y ^ 2 / 2) := by
        rw [hZdef, ← hsumV]
        have h0 : ∑ y, p y * (1 + c y) = 1 := by
          simp only [mul_add, mul_one, sum_add_distrib, htot, hEc, add_zero]
        conv_lhs => rw [← h0]
        rw [sum_div]
        simp only [← sum_sub_distrib]
        exact sum_congr rfl fun y _ => by ring
      rw [e]
      calc |∑ y, p y * (Real.exp (c y) - 1 - c y - c y ^ 2 / 2)|
          ≤ ∑ y, |p y * (Real.exp (c y) - 1 - c y - c y ^ 2 / 2)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ y, p y * (ρ * c y ^ 2) := by
            refine sum_le_sum fun y _ => ?_
            rw [abs_mul, abs_of_pos (hpos y)]
            exact mul_le_mul_of_nonneg_left ((hexp3 y).trans (hcube y)) (hpos y).le
        _ = ρ * V := by
            rw [← hsumV, mul_sum]
            exact sum_congr rfl fun y _ => by ring
    -- `KL = T / Z - log Z`
    have hKL : klDiv (gibbsPolicy β r p) p = T / Z - Real.log Z := by
      rw [klDiv]
      have h1 : ∀ y, gibbsPolicy β r p y * Real.log (gibbsPolicy β r p y / p y)
          = p y * c y * Real.exp (c y) / Z - Real.log Z * (p y * Real.exp (c y) / Z) := by
        intro y
        rw [hπ y]
        have hp0 : p y ≠ 0 := (hpos y).ne'
        have h2 : p y * Real.exp (c y) / Z / p y = Real.exp (c y) / Z := by
          field_simp
        rw [h2, Real.log_div (Real.exp_pos _).ne' hZne, Real.log_exp]
        ring
      rw [sum_congr rfl fun y _ => h1 y, sum_sub_distrib, ← sum_div, ← mul_sum, ← sum_div, ← hZdef,
        div_self hZne, mul_one]
    -- assemble: `-(2ρV + V²) ≤ KL - V/2 ≤ 2ρV`
    have hρ1 : ρ ≤ 1 := by
      rw [hρdef, div_le_one hβ]
      exact hr
    have hKLbound : |klDiv (gibbsPolicy β r p) p - V / 2| ≤ 2 * (ρ * V) + 3 * V ^ 2 := by
      rw [hKL]
      have hTl := (abs_le.1 hT).1
      have hTu := (abs_le.1 hT).2
      have hδl := (abs_le.1 hδ).1
      have hδu := (abs_le.1 hδ).2
      have hρV : 0 ≤ ρ * V := mul_nonneg hρ0 hV0
      have hlogU : Real.log Z ≤ Z - 1 := Real.log_le_sub_one_of_pos hZpos
      have hlogL : 1 - Z⁻¹ ≤ Real.log Z := Real.one_sub_inv_le_log_of_pos hZpos
      rw [abs_le]
      constructor
      · -- lower bound
        have hVρ : 0 ≤ V - ρ * V := by
          have e : V - ρ * V = V * (1 - ρ) := by ring
          rw [e]
          exact mul_nonneg hV0 (by linarith)
        have h1 : (V - ρ * V) / Z ≤ T / Z := div_le_div_of_nonneg_right (by linarith) hZpos.le
        have h2 : (V - ρ * V) * (2 - Z) ≤ (V - ρ * V) / Z := by
          rw [le_div_iff₀ hZpos]
          have e : V - ρ * V - (V - ρ * V) * (2 - Z) * Z = (V - ρ * V) * (Z - 1) ^ 2 := by ring
          have h5 := mul_nonneg hVρ (sq_nonneg (Z - 1))
          linarith
        have h3 : V - ρ * V - (Z - 1) * V ≤ (V - ρ * V) * (2 - Z) := by
          have e : (V - ρ * V) * (2 - Z) = V - ρ * V - (Z - 1) * V + (Z - 1) * (ρ * V) := by ring
          have h5 := mul_nonneg (by linarith : (0 : ℝ) ≤ Z - 1) hρV
          linarith
        have h4 : (Z - 1) * V ≤ V ^ 2 := by
          have e : V ^ 2 = V * V := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right (by linarith) hV0
        have h6 := sq_nonneg V
        linarith
      · -- upper bound
        have h1 : T / Z - Real.log Z ≤ (T - (Z - 1)) / Z := by
          have e : (T - (Z - 1)) / Z = T / Z - (1 - Z⁻¹) := by
            field_simp
          rw [e]
          linarith
        have h2 : (T - (Z - 1)) / Z ≤ V / 2 + 2 * (ρ * V) := by
          rw [div_le_iff₀ hZpos]
          have e : (V / 2 + 2 * (ρ * V)) * Z = (V / 2 + 2 * (ρ * V)) + (V / 2 + 2 * (ρ * V)) * (Z - 1) := by
            ring
          have h5 := mul_nonneg (by linarith : (0 : ℝ) ≤ V / 2 + 2 * (ρ * V))
            (by linarith : (0 : ℝ) ≤ Z - 1)
          linarith
        have h6 := sq_nonneg V
        linarith
    have e1 : rewardRange r * variance p r / β ^ 3 = ρ * V := by
      rw [hρdef, hVdef]
      field_simp
    have e2 : variance p r ^ 2 / β ^ 4 = V ^ 2 := by
      rw [hVdef]
      field_simp
    rw [e1, e2]
    exact hKLbound
  -- so `β² KL → Var/2`
  have hlimKL : Tendsto (fun β : ℝ => β ^ 2 * klDiv (gibbsPolicy β r p) p) atTop
      (nhds (variance p r / 2)) := by
    have hE : Tendsto (fun β : ℝ => 2 * (rewardRange r * variance p r) / β
        + 3 * variance p r ^ 2 / β ^ 2) atTop (nhds 0) := by
      have h1 := (tendsto_const_nhds (x := 2 * (rewardRange r * variance p r))).div_atTop
        tendsto_id
      have h2 := (tendsto_const_nhds (x := 3 * variance p r ^ 2)).div_atTop
        (tendsto_pow_atTop (two_ne_zero))
      simpa using h1.add h2
    have hlo := (tendsto_const_nhds (x := variance p r / 2)).sub hE
    have hhi := (tendsto_const_nhds (x := variance p r / 2)).add hE
    rw [sub_zero] at hlo
    rw [add_zero] at hhi
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
    · filter_upwards [eventually_ge_atTop (max (rewardRange r) 1)] with β hβ
      have hβpos : 0 < β := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hβ)
      have h1 := (abs_le.1 (hb β hβpos (le_trans (le_max_left _ _) hβ))).1
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg β)
      have e1 : β ^ 2 * -(2 * (rewardRange r * variance p r / β ^ 3)
          + 3 * (variance p r ^ 2 / β ^ 4))
          = -(2 * (rewardRange r * variance p r) / β + 3 * variance p r ^ 2 / β ^ 2) := by
        field_simp
      have e2 : β ^ 2 * (klDiv (gibbsPolicy β r p) p - variance p r / β ^ 2 / 2)
          = β ^ 2 * klDiv (gibbsPolicy β r p) p - variance p r / 2 := by
        field_simp
      rw [e1, e2] at h2
      linarith
    · filter_upwards [eventually_ge_atTop (max (rewardRange r) 1)] with β hβ
      have hβpos : 0 < β := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hβ)
      have h1 := (abs_le.1 (hb β hβpos (le_trans (le_max_left _ _) hβ))).2
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg β)
      have e1 : β ^ 2 * (2 * (rewardRange r * variance p r / β ^ 3)
          + 3 * (variance p r ^ 2 / β ^ 4))
          = 2 * (rewardRange r * variance p r) / β + 3 * variance p r ^ 2 / β ^ 2 := by
        field_simp
      have e2 : β ^ 2 * (klDiv (gibbsPolicy β r p) p - variance p r / β ^ 2 / 2)
          = β ^ 2 * klDiv (gibbsPolicy β r p) p - variance p r / 2 := by
        field_simp
      rw [e1, e2] at h2
      linarith
  -- `β √(2 KL) = √(2 · β² KL)` for `β > 0`
  have h := ((hlimKL.const_mul 2).sqrt)
  have e : 2 * (variance p r / 2) = variance p r := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with β hβ
  rw [show 2 * (β ^ 2 * klDiv (gibbsPolicy β r p) p) = β ^ 2 * (2 * klDiv (gibbsPolicy β r p) p)
    by ring, Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ.le]
