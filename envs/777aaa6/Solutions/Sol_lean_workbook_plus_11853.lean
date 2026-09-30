-- Prove2me | solution 1 for lean_workbook_plus_11853
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:53:53.20118+00:00
-- url     : https://prove2.me/submissions/fd95961d-2b2f-4841-85c9-397c7ca392e1

import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem solution (f : ℝ → ℝ)
    (h1 : ∃ M, ∀ x ∈ Set.Icc (0 : ℝ) 2, abs (f x) ≤ M)
    (h2 : ∀ x y, x ≥ 0 ∧ y ≥ 0 ∧ x + y ≤ 2 →
      f (x + y) ≥ 1 + 2 * y * (f x)^2) : False := by
  have hf0 : 1 ≤ f 0 := by simpa using h2 0 0 (by norm_num)
  have hf0pos : 0 < f 0 := by linarith
  -- The reciprocal potential keeps the growing iterates inside the interval.
  have hw : ∀ n : ℕ, ∃ x : ℝ,
      0 ≤ x ∧ 0 < f x ∧ x + 2 / f x ≤ 2 ∧ (2 : ℝ)^n ≤ f x := by
    intro n
    induction n with
    | zero =>
      refine ⟨0, le_refl _, hf0pos, ?_, ?_⟩
      · simpa using (div_le_iff₀ hf0pos).2 (by linarith : (2 : ℝ) ≤ 2 * f 0)
      · simpa using hf0
    | succ n ih =>
      obtain ⟨x, hx, hfx, hpot, hgrowth⟩ := ih
      have hy : 0 < 1 / f x := one_div_pos.mpr hfx
      have htwice : 2 / f x = 1 / f x + 1 / f x := by ring
      have hxy : x + 1 / f x ≤ 2 := by rw [htwice] at hpot; linarith
      have hstep := h2 x (1 / f x) ⟨hx, hy.le, hxy⟩
      have hid : 1 + 2 * (1 / f x) * (f x)^2 = 1 + 2 * f x := by
        field_simp [ne_of_gt hfx]
      rw [hid] at hstep
      have hnext : 0 < f (x + 1 / f x) := by linarith
      have hrecip : 2 / f (x + 1 / f x) ≤ 1 / f x :=
        (div_le_div_iff₀ hnext hfx).2 (by linarith)
      refine ⟨x + 1 / f x, add_nonneg hx hy.le, hnext, ?_, ?_⟩
      · rw [htwice] at hpot
        linarith
      · rw [pow_succ]
        linarith
  obtain ⟨M, hM⟩ := h1
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (by norm_num : (1 : ℝ) < 2)
  obtain ⟨x, hx, hfx, hpot, hgrowth⟩ := hw n
  have hx2 : x ≤ 2 := by
    have hdiv : 0 < 2 / f x := div_pos (by norm_num) hfx
    linarith
  have hbound := hM x ⟨hx, hx2⟩
  rw [abs_of_pos hfx] at hbound
  linarith
