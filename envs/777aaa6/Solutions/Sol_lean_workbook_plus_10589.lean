-- Prove2me | solution 1 for lean_workbook_plus_10589
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:41:34.65488+00:00
-- url     : https://prove2.me/submissions/71e61751-7a5f-43bc-9891-43e6777b36ed

import Mathlib

/-- Two-sided Taylor bounds for `exp (-u)` on `[0,1]` from `Real.exp_bound` with 7 terms. -/
lemma expNegLB (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 - u + u^2/2 - u^3/6 + u^4/24 - u^5/120 + u^6/720 - u^7 * (8/35280) ≤ Real.exp (-u) := by
  have h := Real.exp_bound (x := -u) (by rw [abs_neg, abs_of_nonneg hu0]; exact hu1) (n := 7) (by norm_num)
  rw [abs_neg, abs_of_nonneg hu0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.1, h.2]

lemma expNegUB (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (-u) ≤ 1 - u + u^2/2 - u^3/6 + u^4/24 - u^5/120 + u^6/720 + u^7 * (8/35280) := by
  have h := Real.exp_bound (x := -u) (by rw [abs_neg, abs_of_nonneg hu0]; exact hu1) (n := 7) (by norm_num)
  rw [abs_neg, abs_of_nonneg hu0] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.1, h.2]

/-- Lower bound for `q - q^2` when `a ≤ q ≤ b`. -/
lemma term_lb {q a b c : ℝ} (ha : a ≤ q) (hb : q ≤ b) (hc1 : c ≤ a - a^2) (hc2 : c ≤ b - b^2) :
    c ≤ q - q^2 := by
  rcases le_or_gt (a + b) 1 with h | h
  · nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb), mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 h)]
  · nlinarith [mul_nonneg (sub_nonneg.2 ha) (sub_nonneg.2 hb), mul_nonneg (sub_nonneg.2 hb) (sub_nonneg.2 h.le)]

theorem solution (f : ℝ → ℝ) (hf: ContinuousOn f (Set.Icc 0 1)) (hx: ∀ x ∈ (Set.Icc 0 1), f (x^2) + f x = x) : ∀ x ∈ (Set.Icc 0 1), f x = x - x^2 := by
  exfalso
  have f0 : f 0 = 0 := by
    have := hx 0 (by norm_num); norm_num at this; linarith
  have f1 : f 1 = 1/2 := by
    have := hx 1 (by norm_num); norm_num at this; linarith
  have step : ∀ y ∈ Set.Icc (0:ℝ) 1, f y - f (y^4) = y - y^2 := by
    intro y hy
    have h1 := hx y hy
    have h2 := hx (y^2) ⟨by positivity, pow_le_one₀ hy.1 hy.2⟩
    have e : (y^2)^2 = y^4 := by ring
    rw [e] at h2
    linarith
  have tele : ∀ r ∈ Set.Icc (0:ℝ) 1, ∀ L : ℕ,
      f r - f (r^(4^L)) = ∑ j ∈ Finset.range L, (r^(4^j) - (r^(4^j))^2) := by
    intro r hr L
    induction L with
    | zero => simp
    | succ L ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hmem : r^(4^L) ∈ Set.Icc (0:ℝ) 1 := ⟨pow_nonneg hr.1 _, pow_le_one₀ hr.1 hr.2⟩
      have h := step _ hmem
      have e : (r^(4^L))^4 = r^(4^(L+1)) := by rw [← pow_mul, pow_succ]
      rw [e] at h
      linarith
  -- continuity at 1 and at 0
  obtain ⟨δ₁, hδ₁, hc1⟩ := Metric.continuousOn_iff.mp hf 1 (by norm_num) (1/1000) (by norm_num)
  obtain ⟨δ₀, hδ₀, hc0⟩ := Metric.continuousOn_iff.mp hf 0 (by norm_num) (1/1000) (by norm_num)
  -- choose N with (7/5)/4^N < δ₁ and N ≥ 6
  obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt ((7/5) / δ₁) (by norm_num : (1:ℝ) < 4)
  obtain ⟨N, hN6, h4N⟩ : ∃ N : ℕ, 6 ≤ N ∧ (7/5) / δ₁ < (4:ℝ)^N :=
    ⟨max N₀ 6, le_max_right _ _,
      lt_of_lt_of_le hN₀ (pow_le_pow_right₀ (by norm_num) (le_max_left _ _))⟩
  set t : ℝ := (7/5) / 4^N with ht
  have ht_pos : 0 < t := by positivity
  have ht_lt : t < δ₁ := by
    rw [ht, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ₁] at h4N
    linarith
  set r : ℝ := Real.exp (-t) with hr
  have hr_pos : 0 < r := Real.exp_pos _
  have hr_lt : r < 1 := by rw [hr, Real.exp_lt_one_iff]; linarith
  have hr_mem : r ∈ Set.Icc (0:ℝ) 1 := ⟨hr_pos.le, hr_lt.le⟩
  have hr_ge : 1 - t ≤ r := Real.one_sub_le_exp_neg t
  have hfr : |f r - 1/2| < 1/1000 := by
    have := hc1 r hr_mem (by rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith)
    rw [Real.dist_eq, f1] at this; exact this
  -- choose K ≥ 2 with 1/δ₀ < 4^K, and L = N + K
  obtain ⟨K₀, hK₀⟩ := pow_unbounded_of_one_lt (1 / δ₀) (by norm_num : (1:ℝ) < 4)
  obtain ⟨K, hK2, h4K⟩ : ∃ K : ℕ, 2 ≤ K ∧ 1 / δ₀ < (4:ℝ)^K :=
    ⟨max K₀ 2, le_max_right _ _,
      lt_of_lt_of_le hK₀ (pow_le_pow_right₀ (by norm_num) (le_max_left _ _))⟩
  set L := N + K with hL
  have hsmall : r^(4^L) < δ₀ := by
    have e1 : r^(4^L) = Real.exp (-((7/5) * 4^K)) := by
      rw [hr, ← Real.exp_nat_mul]
      congr 1
      rw [hL, pow_add, ht]; push_cast; field_simp
    rw [e1, Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) hδ₀]
    have h1 : (7/5) * (4:ℝ)^K + 1 ≤ Real.exp ((7/5) * 4^K) := Real.add_one_le_exp _
    have h2 : (0:ℝ) ≤ 4^K := by positivity
    rw [one_div] at h4K
    linarith
  have hfs : |f (r^(4^L))| < 1/1000 := by
    have hmem : r^(4^L) ∈ Set.Icc (0:ℝ) 1 := ⟨pow_nonneg hr_pos.le _, pow_le_one₀ hr_pos.le hr_lt.le⟩
    have := hc0 _ hmem (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hr_pos.le _)]; exact hsmall)
    rw [Real.dist_eq, f0, sub_zero] at this; exact this
  -- upper bound on the telescoped sum
  have hsum_upper : ∑ j ∈ Finset.range L, (r^(4^j) - (r^(4^j))^2) < 1/2 + 2/1000 := by
    rw [← tele r hr_mem L]
    rw [abs_sub_lt_iff] at hfr; rw [abs_lt] at hfs
    linarith
  -- lower bound: restrict to the window j ∈ [N-6, N+2)
  have hterm_nonneg : ∀ j, 0 ≤ r^(4^j) - (r^(4^j))^2 := by
    intro j
    have h1 : 0 ≤ r^(4^j) := pow_nonneg hr_pos.le _
    have h2 : r^(4^j) ≤ 1 := pow_le_one₀ hr_pos.le hr_lt.le
    nlinarith
  have hsub : Finset.Ico (N-6) (N+2) ⊆ Finset.range L := by
    intro j hj
    rw [Finset.mem_Ico] at hj; rw [Finset.mem_range]
    omega
  have hsum_lower : ∑ j ∈ Finset.Ico (N-6) (N+2), (r^(4^j) - (r^(4^j))^2)
      ≤ ∑ j ∈ Finset.range L, (r^(4^j) - (r^(4^j))^2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hterm_nonneg j)
  have hIco : ∑ j ∈ Finset.Ico (N-6) (N+2), (r^(4^j) - (r^(4^j))^2)
      = ∑ i ∈ Finset.range 8, (Real.exp (-(7 * 4^i / 20480)) - Real.exp (-(7 * 4^i / 20480))^2) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have e : N + 2 - (N - 6) = 8 := by omega
    rw [e]
    apply Finset.sum_congr rfl
    intro i _
    have e2 : r^(4^(N-6+i)) = Real.exp (-(7 * 4^i / 20480)) := by
      rw [hr, ← Real.exp_nat_mul]
      congr 1
      rw [ht]
      have e3 : (4:ℝ)^N = 4^(N-6) * 4^6 := by rw [← pow_add]; congr 1; omega
      rw [e3]; push_cast; rw [pow_add]; field_simp; ring
    rw [e2]
  rw [hIco] at hsum_lower
  -- numeric evaluation of the eight terms
  have hq7 := expNegLB (7/10) (by norm_num) (by norm_num)
  have hq7' := expNegUB (7/10) (by norm_num) (by norm_num)
  have e6 : Real.exp (-(7 * 4^6 / 20480)) = Real.exp (-(7/10)) ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have e7 : Real.exp (-(7 * 4^7 / 20480)) = Real.exp (-(7/10)) ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  have T0 : (0.000341621:ℝ) ≤ Real.exp (-(7 * 4^0 / 20480)) - Real.exp (-(7 * 4^0 / 20480))^2 := by
    have hl := expNegLB (7 * 4^0 / 20480) (by norm_num) (by norm_num)
    have hu := expNegUB (7 * 4^0 / 20480) (by norm_num) (by norm_num)
    exact term_lb hl hu (by norm_num) (by norm_num)
  have T1 : (0.001364386:ℝ) ≤ Real.exp (-(7 * 4^1 / 20480)) - Real.exp (-(7 * 4^1 / 20480))^2 := by
    have hl := expNegLB (7 * 4^1 / 20480) (by norm_num) (by norm_num)
    have hu := expNegUB (7 * 4^1 / 20480) (by norm_num) (by norm_num)
    exact term_lb hl hu (by norm_num) (by norm_num)
  have T2 : (0.005424079:ℝ) ≤ Real.exp (-(7 * 4^2 / 20480)) - Real.exp (-(7 * 4^2 / 20480))^2 := by
    have hl := expNegLB (7 * 4^2 / 20480) (by norm_num) (by norm_num)
    have hu := expNegUB (7 * 4^2 / 20480) (by norm_num) (by norm_num)
    exact term_lb hl hu (by norm_num) (by norm_num)
  have T3 : (0.021169296:ℝ) ≤ Real.exp (-(7 * 4^3 / 20480)) - Real.exp (-(7 * 4^3 / 20480))^2 := by
    have hl := expNegLB (7 * 4^3 / 20480) (by norm_num) (by norm_num)
    have hu := expNegUB (7 * 4^3 / 20480) (by norm_num) (by norm_num)
    exact term_lb hl hu (by norm_num) (by norm_num)
  have T4 : (0.07676185:ℝ) ≤ Real.exp (-(7 * 4^4 / 20480)) - Real.exp (-(7 * 4^4 / 20480))^2 := by
    have hl := expNegLB (7 * 4^4 / 20480) (by norm_num) (by norm_num)
    have hu := expNegUB (7 * 4^4 / 20480) (by norm_num) (by norm_num)
    exact term_lb hl hu (by norm_num) (by norm_num)
  have T5 : (0.208102676:ℝ) ≤ Real.exp (-(7 * 4^5 / 20480)) - Real.exp (-(7 * 4^5 / 20480))^2 := by
    have hl := expNegLB (7 * 4^5 / 20480) (by norm_num) (by norm_num)
    have hu := expNegUB (7 * 4^5 / 20480) (by norm_num) (by norm_num)
    exact term_lb hl hu (by norm_num) (by norm_num)
  have T6 : (0.185785058:ℝ) ≤ Real.exp (-(7 * 4^6 / 20480)) - Real.exp (-(7 * 4^6 / 20480))^2 := by
    rw [e6]
    have hl : (0.4965816436:ℝ)^2 ≤ Real.exp (-(7/10)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hu : Real.exp (-(7/10)) ^ 2 ≤ (0.4966189925:ℝ)^2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le (by linarith) 2
    exact term_lb hl hu (by norm_num) (by norm_num)
  have T7 : (0.003683973:ℝ) ≤ Real.exp (-(7 * 4^7 / 20480)) - Real.exp (-(7 * 4^7 / 20480))^2 := by
    rw [e7]
    have hl : (0.4965816436:ℝ)^8 ≤ Real.exp (-(7/10)) ^ 8 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 8
    have hu : Real.exp (-(7/10)) ^ 8 ≤ (0.4966189925:ℝ)^8 :=
      pow_le_pow_left₀ (Real.exp_pos _).le (by linarith) 8
    exact term_lb hl hu (by norm_num) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsum_lower
  linarith
