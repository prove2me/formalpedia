-- Prove2me | solution 1 for BookSixth.alltime_line_relabel_map
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T20:01:37.825525+00:00
-- url     : https://prove2.me/submissions/312a13b8-9cdf-4e50-84e6-0834e3cec785

import Mathlib

theorem solution (a b : ℝ) (hL : 0 < b - a - 2) :
    ∃ f : ℝ → (ℝ → ℝ),
      (∀ t, Continuous (f t)) ∧
      (∀ x, f 0 x = x) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 → f t (a + u) = a * (1 - max 0 (min t 1)) + u) ∧
      (∀ t u, -1 ≤ u → u ≤ 1 →
        f t (b + u) = b * (1 - max 0 (min t 1)) + 3 * max 0 (min t 1) + u) := by
  refine ⟨fun t x => x - a * max 0 (min t 1) +
    (a + 3 - b) * max 0 (min t 1) *
      max 0 (min ((x - a - 1) / (b - a - 2)) 1), ?_, ?_, ?_, ?_⟩
  · intro t
    fun_prop
  · intro x
    simp
  · intro t u _ hu
    dsimp only
    have h : (a + u - a - 1) / (b - a - 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hL.le
    rw [min_eq_left (show (a + u - a - 1) / (b - a - 2) ≤ 1 by linarith), max_eq_left h]
    ring
  · intro t u hu _
    dsimp only
    have h : 1 ≤ (b + u - a - 1) / (b - a - 2) :=
      (le_div_iff₀ hL).2 (by linarith)
    rw [min_eq_right h]
    norm_num
    ring
