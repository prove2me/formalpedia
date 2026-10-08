-- Prove2me | solution 2 for BookSixth.pair_relabel_line_alltime_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T15:52:25.274751+00:00
-- url     : https://prove2.me/submissions/e5f88f62-9800-4e58-a524-5843e6c534f5

import Mathlib

theorem solution (a b : ℝ) (g : ℝ ≃ₜ ℝ)
    (hglo : ∀ u, -1 ≤ u → u ≤ 1 → g (a + u) = u)
    (hghi : ∀ u, -1 ≤ u → u ≤ 1 → g (b + u) = 3 + u) :
    ∃ F : ℝ → (ℝ ≃ₜ ℝ),
      Continuous (fun p : ℝ × ℝ => (F p.1) p.2) ∧
      Continuous (fun p : ℝ × ℝ => (F p.1).symm p.2) ∧
      (∀ x, F 0 x = x) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 →
        F t (a + u) = a * (1 - max 0 (min t 1)) + u) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 →
        F t (b + u) = b * (1 - max 0 (min t 1)) + 3 * max 0 (min t 1) + u) := by
  have hmono : StrictMono g ∨ StrictAnti g :=
    g.continuous.strictMono_of_inj g.injective
  have h1 := hglo 1 (by norm_num) le_rfl
  have h2 := hglo (-1) le_rfl (by norm_num)
  have h3 := hghi (-1) le_rfl (by norm_num)
  have hcd : a + 1 < b - 1 := by
    rcases hmono with hm | hm
    · have : g (a + 1) < g (b + -1) := by rw [h1, h3]; norm_num
      have := hm.lt_iff_lt.mp this; linarith
    · exact absurd (hm (show a + -1 < a + 1 by linarith)) (by rw [h1, h2]; norm_num)
  set D := (b - 1) - (a + 1) with hD
  have hDpos : 0 < D := by rw [hD]; linarith
  set k := 3 - b + a with hk
  let τ : ℝ → ℝ := fun t => max 0 (min t 1)
  have hτ0 : ∀ t, 0 ≤ τ t := fun t => le_max_left _ _
  have hτ1 : ∀ t, τ t ≤ 1 := fun t => max_le zero_le_one (min_le_right _ _)
  have hDt : ∀ t, 0 < D + k * τ t := by
    intro t
    have := hτ0 t; have := hτ1 t
    have e : D + k * τ t = D * (1 - τ t) + τ t := by rw [hD, hk]; ring
    rw [e]
    rcases eq_or_lt_of_le (hτ0 t) with h | h
    · rw [← h]; simpa using hDpos
    · nlinarith
  let f : ℝ → ℝ → ℝ := fun t x =>
    x + τ t * (-a + k * (max 0 (min (x - (a + 1)) D) / D))
  let h : ℝ → ℝ → ℝ := fun t y =>
    y + a * τ t - k * τ t * (max 0 (min (y - (a + 1 - a * τ t)) (D + k * τ t)) / (D + k * τ t))
  have key1 : ∀ t x, max 0 (min (f t x - (a + 1 - a * τ t)) (D + k * τ t)) / (D + k * τ t)
      = max 0 (min (x - (a + 1)) D) / D := by
    intro t x
    have hp := hDt t; have := hτ0 t
    simp only [f]
    rcases le_total x (a + 1) with hx | hx
    · have e1 : max 0 (min (x - (a + 1)) D) = 0 := by
        apply max_eq_left; exact le_trans (min_le_left _ _) (by linarith)
      rw [e1]
      have e2 : max 0 (min (x + τ t * (-a + k * (0 / D)) - (a + 1 - a * τ t)) (D + k * τ t)) = 0 := by
        apply max_eq_left; refine le_trans (min_le_left _ _) ?_; simp; linarith
      rw [e2]; simp
    rcases le_total x (b - 1) with hx' | hx'
    · have e1 : max 0 (min (x - (a + 1)) D) = x - (a + 1) := by
        rw [min_eq_left (by rw [hD]; linarith), max_eq_right (by linarith)]
      rw [e1]
      have e3 : x + τ t * (-a + k * ((x - (a + 1)) / D)) - (a + 1 - a * τ t)
          = (x - (a + 1)) / D * (D + k * τ t) := by field_simp; ring
      rw [e3, min_eq_left, max_eq_right]
      · field_simp
      · positivity
      · have : (x - (a + 1)) / D ≤ 1 := by rw [div_le_one hDpos]; rw [hD]; linarith
        nlinarith
    · have e1 : max 0 (min (x - (a + 1)) D) = D := by
        rw [min_eq_right (by rw [hD]; linarith), max_eq_right hDpos.le]
      rw [e1, div_self hDpos.ne']
      rw [min_eq_right, max_eq_right hp.le, div_self hp.ne']
      have : k * τ t = k * τ t := rfl
      rw [hD] at *; nlinarith
  have key2 : ∀ t y, max 0 (min (h t y - (a + 1)) D) / D
      = max 0 (min (y - (a + 1 - a * τ t)) (D + k * τ t)) / (D + k * τ t) := by
    intro t y
    have hp := hDt t; have := hτ0 t
    simp only [h]
    set E := D + k * τ t
    rcases le_total y (a + 1 - a * τ t) with hy | hy
    · have e1 : max 0 (min (y - (a + 1 - a * τ t)) E) = 0 := by
        apply max_eq_left; exact le_trans (min_le_left _ _) (by linarith)
      rw [e1]
      have e2 : max 0 (min (y + a * τ t - k * τ t * (0 / E) - (a + 1)) D) = 0 := by
        apply max_eq_left; refine le_trans (min_le_left _ _) ?_; simp; linarith
      rw [e2]; simp
    rcases le_total (y - (a + 1 - a * τ t)) E with hy' | hy'
    · have e1 : max 0 (min (y - (a + 1 - a * τ t)) E) = y - (a + 1 - a * τ t) := by
        rw [min_eq_left hy', max_eq_right (by linarith)]
      rw [e1]
      have e3 : y + a * τ t - k * τ t * ((y - (a + 1 - a * τ t)) / E) - (a + 1)
          = (y - (a + 1 - a * τ t)) / E * D := by
        field_simp; simp only [E]; ring
      rw [e3, min_eq_left, max_eq_right]
      · field_simp
      · have : 0 ≤ (y - (a + 1 - a * τ t)) / E := div_nonneg (by linarith) hp.le
        positivity
      · have : (y - (a + 1 - a * τ t)) / E ≤ 1 := by rw [div_le_one hp]; exact hy'
        nlinarith
    · have e1 : max 0 (min (y - (a + 1 - a * τ t)) E) = E := by
        rw [min_eq_right hy', max_eq_right hp.le]
      rw [e1, div_self hp.ne', mul_one]
      rw [min_eq_right, max_eq_right hDpos.le, div_self hDpos.ne']
      simp only [E] at hy'; linarith
  have lf : ∀ t x, h t (f t x) = x := by
    intro t x
    have := key1 t x
    simp only [h] at *; rw [this]; simp only [f]; ring
  have rf : ∀ t y, f t (h t y) = y := by
    intro t y
    have := key2 t y
    simp only [f] at *; rw [this]; simp only [h]; ring
  have cf : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := by
    simp only [f, τ]; fun_prop
  have ch : Continuous (fun p : ℝ × ℝ => h p.1 p.2) := by
    simp only [h]
    refine Continuous.sub (by simp only [τ]; fun_prop) (Continuous.mul (by simp only [τ]; fun_prop) ?_)
    refine Continuous.div (by simp only [τ]; fun_prop) (by simp only [τ]; fun_prop) ?_
    intro p; exact (hDt p.1).ne'
  let F : ℝ → (ℝ ≃ₜ ℝ) := fun t =>
    { toFun := f t, invFun := h t, left_inv := lf t, right_inv := rf t
      continuous_toFun := cf.comp (Continuous.prodMk continuous_const continuous_id)
      continuous_invFun := ch.comp (Continuous.prodMk continuous_const continuous_id) }
  refine ⟨F, cf, ch, ?_, ?_, ?_⟩
  · intro x; show f 0 x = x; simp [f, τ]
  · intro t u hu1 hu2
    show f t (a + u) = _
    have e1 : max 0 (min (a + u - (a + 1)) D) = 0 := by
      apply max_eq_left; exact le_trans (min_le_left _ _) (by linarith)
    simp only [f]; rw [e1]; simp only [τ]; ring
  · intro t u hu1 hu2
    show f t (b + u) = _
    have e1 : max 0 (min (b + u - (a + 1)) D) = D := by
      rw [min_eq_right (by rw [hD]; linarith), max_eq_right hDpos.le]
    simp only [f]; rw [e1, div_self hDpos.ne']; simp only [τ, hk]; ring
