-- Prove2me | solution 1 for BookSixth.alltime_line_relabel_exists
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T15:22:28.988882+00:00
-- url     : https://prove2.me/submissions/3cc48c63-2805-42df-8e88-21966242bacb

import Mathlib

theorem solution (a b : ℝ) (hL : 0 < b - a - 2) :
    ∃ F : ℝ → (ℝ ≃ₜ ℝ),
      Continuous (fun p : ℝ × ℝ => (F p.1) p.2) ∧
      Continuous (fun p : ℝ × ℝ => (F p.1).symm p.2) ∧
      (∀ x, F 0 x = x) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 →
        F t (a + u) = a * (1 - max 0 (min t 1)) + u) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 →
        F t (b + u) = b * (1 - max 0 (min t 1)) + 3 * max 0 (min t 1) + u) := by
  set L := b - a - 2 with hLdef
  have hM : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 → 0 < 1 - τ + τ / L := by
    intro τ h0 h1
    have : 0 ≤ τ / L := div_nonneg h0 hL.le
    rcases eq_or_lt_of_le h1 with h | h
    · subst h; simpa using hL
    · linarith
  have hML : ∀ τ : ℝ, (1 - τ + τ / L) * L = L - τ * L + τ := by
    intro τ; field_simp
  let f : ℝ → ℝ → ℝ → ℝ := fun τ M x =>
    x - τ * a + (M - 1) * (max (a + 1) (min x (b - 1)) - (a + 1))
  let g : ℝ → ℝ → ℝ → ℝ := fun τ M y =>
    y + τ * a - (1 - 1 / M) *
      (max (a + 1 - τ * a) (min y (b - 1 + τ * (3 - b))) - (a + 1 - τ * a))
  have lft : ∀ τ M : ℝ, 0 ≤ τ → τ ≤ 1 → 0 < M → M * L = L - τ * L + τ →
      ∀ x, g τ M (f τ M x) = x := by
    intro τ M h0 h1 hm hml x
    have hab : a + 1 - τ * a ≤ b - 1 + τ * (3 - b) := by
      nlinarith [mul_nonneg (sub_nonneg.2 h1) hL.le]
    simp only [f, g]
    rcases le_or_gt x (a + 1) with hx | hx
    · rw [min_eq_left (by linarith), max_eq_left hx]
      rw [min_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    rcases le_or_gt x (b - 1) with hx2 | hx2
    · rw [min_eq_left hx2, max_eq_right hx.le]
      have e1 : x - τ * a + (M - 1) * (x - (a + 1)) ≤ b - 1 + τ * (3 - b) := by
        nlinarith [mul_le_mul_of_nonneg_left hx2 hm.le]
      have e2 : a + 1 - τ * a ≤ x - τ * a + (M - 1) * (x - (a + 1)) := by
        nlinarith [mul_pos hm (sub_pos.2 hx)]
      rw [min_eq_left e1, max_eq_right e2]
      field_simp; ring
    · rw [min_eq_right hx2.le, max_eq_right (by linarith)]
      have e1 : b - 1 + τ * (3 - b) ≤ x - τ * a + (M - 1) * (b - 1 - (a + 1)) := by
        nlinarith
      rw [min_eq_right e1, max_eq_right hab]
      field_simp; nlinarith
  have rgt : ∀ τ M : ℝ, 0 ≤ τ → τ ≤ 1 → 0 < M → M * L = L - τ * L + τ →
      ∀ y, f τ M (g τ M y) = y := by
    intro τ M h0 h1 hm hml y
    have hab : a + 1 - τ * a ≤ b - 1 + τ * (3 - b) := by
      nlinarith [mul_nonneg (sub_nonneg.2 h1) hL.le]
    simp only [f, g]
    rcases le_or_gt y (a + 1 - τ * a) with hy | hy
    · rw [min_eq_left (by linarith), max_eq_left hy]
      rw [min_eq_left (by linarith), max_eq_left (by linarith)]
      ring
    rcases le_or_gt y (b - 1 + τ * (3 - b)) with hy2 | hy2
    · rw [min_eq_left hy2, max_eq_right hy.le]
      have hk : y + τ * a - (1 - 1 / M) * (y - (a + 1 - τ * a))
          = a + 1 + (y - (a + 1 - τ * a)) / M := by field_simp; ring
      rw [hk]
      have hd : 0 ≤ (y - (a + 1 - τ * a)) / M := div_nonneg (by linarith) hm.le
      have hd2 : (y - (a + 1 - τ * a)) / M ≤ L := by
        rw [div_le_iff₀ hm]; nlinarith
      rw [min_eq_left (by linarith), max_eq_right (by linarith)]
      field_simp; ring
    · rw [min_eq_right hy2.le, max_eq_right hab]
      have hk : y + τ * a - (1 - 1 / M) * (b - 1 + τ * (3 - b) - (a + 1 - τ * a))
          = y - τ * (3 - b) := by
        have : b - 1 + τ * (3 - b) - (a + 1 - τ * a) = M * L := by rw [hml]; ring
        rw [this]; field_simp; nlinarith
      rw [hk]
      rw [min_eq_right (by nlinarith), max_eq_right (by linarith)]
      nlinarith
  let T : ℝ → ℝ := fun t => max 0 (min t 1)
  have T0 : ∀ t, 0 ≤ T t := fun t => le_max_left _ _
  have T1 : ∀ t, T t ≤ 1 := fun t => max_le zero_le_one (min_le_right _ _)
  let Mt : ℝ → ℝ := fun t => 1 - T t + T t / L
  have hMt : ∀ t, 0 < Mt t := fun t => hM _ (T0 t) (T1 t)
  have hMLt : ∀ t, Mt t * L = L - T t * L + T t := fun t => hML _
  refine ⟨fun t => Homeomorph.mk
    { toFun := f (T t) (Mt t), invFun := g (T t) (Mt t),
      left_inv := lft _ _ (T0 t) (T1 t) (hMt t) (hMLt t),
      right_inv := rgt _ _ (T0 t) (T1 t) (hMt t) (hMLt t) }
    (by simp only [f]; fun_prop)
    (by simp only [g]; fun_prop), ?_, ?_, ?_, ?_, ?_⟩
  · show Continuous fun p : ℝ × ℝ => f (T p.1) (Mt p.1) p.2
    simp only [f, Mt, T]; fun_prop
  · show Continuous fun p : ℝ × ℝ => g (T p.1) (Mt p.1) p.2
    simp only [g]
    apply Continuous.sub (by simp only [T]; fun_prop)
    apply Continuous.mul _ (by simp only [T]; fun_prop)
    apply continuous_const.sub
    apply Continuous.div continuous_const (by simp only [Mt, T]; fun_prop)
    intro p; exact (hMt _).ne'
  · intro x
    show f (T 0) (Mt 0) x = x
    simp [f, Mt, T]
  · intro t u hu1 hu2
    show f (T t) (Mt t) (a + u) = a * (1 - T t) + u
    simp only [f]
    rw [min_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  · intro t u hu1 hu2
    show f (T t) (Mt t) (b + u) = b * (1 - T t) + 3 * T t + u
    have hml := hMLt t
    simp only [f]
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    nlinarith
