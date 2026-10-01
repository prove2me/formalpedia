-- Prove2me | solution 1 for BookSixth.pair_relabel_line_gap_algebra
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:04:20.31116+00:00
-- url     : https://prove2.me/submissions/cec675b4-3c02-4eb7-ae98-6b5c3ad96786

import Mathlib

private lemma clamp_bounds (t : ℝ) : 0 ≤ max 0 (min t 1) ∧ max 0 (min t 1) ≤ 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

private lemma gap_pos {a b : ℝ} (h : 3 ≤ b - a) (t : ℝ) :
    0 < (b - 1 + (3 - b) * max 0 (min t 1)) - (a + 1 - a * max 0 (min t 1)) := by
  have hb := clamp_bounds t
  nlinarith [mul_nonneg (show 0 ≤ b-a-3 by linarith) (sub_nonneg.mpr hb.2)]

theorem solution :
    (Continuous (fun t : ℝ => max 0 (min t 1))) ∧
    ((max 0 (min 0 1)) = 0) ∧
    ((max 0 (min 1 1)) = 1) ∧
    (∀ t : ℝ, 0 ≤ max 0 (min t 1)) ∧
    (∀ t : ℝ, max 0 (min t 1) ≤ 1) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → 0 < b - a - 2) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → ∀ t : ℝ,
      0 < (b - 1 + (3 - b) * max 0 (min t 1)) - (a + 1 - a * max 0 (min t 1))) ∧
    (∀ a b t : ℝ,
      (b - 1 + (3 - b) * max 0 (min t 1)) - (a + 1 - a * max 0 (min t 1))
        = 1 + (b - a - 3) * (1 - max 0 (min t 1))) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → ∀ t : ℝ,
      a + 1 - a * max 0 (min t 1)
        = (a + 1 - a * max 0 (min t 1))
          + ((a + 1 - (a + 1)) * ((b - 1 + (3 - b) * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1))) / (b - a - 2))) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → ∀ t : ℝ,
      (a + 1 - a * max 0 (min t 1))
          + ((b - 1 - (a + 1)) * ((b - 1 + (3 - b) * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1))) / (b - a - 2))
        = b - 1 + (3 - b) * max 0 (min t 1)) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → ∀ t : ℝ,
      a + 1 + (((b - 1 + (3 - b) * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1))) * (b - a - 2)
          / ((b - 1 + (3 - b) * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1))))
        = (b - 1 + (3 - b) * max 0 (min t 1))
          - (3 - b) * max 0 (min t 1)) ∧
    (∀ {a b : ℝ}, 3 ≤ b - a → ∀ t : ℝ,
      (a + 1 - a * max 0 (min t 1)) + a * max 0 (min t 1)
        = a + 1 + (((a + 1 - a * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1))) * (b - a - 2)
          / ((b - 1 + (3 - b) * max 0 (min t 1))
            - (a + 1 - a * max 0 (min t 1)))))  := by
  refine ⟨?_, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro t; exact (clamp_bounds t).1
  · intro t; exact (clamp_bounds t).2
  · intro a b h; linarith
  · intro a b h t; exact gap_pos h t
  · intro a b t; ring
  · intro a b h t; simp
  · intro a b h t
    have hd : b-a-2 ≠ 0 := by linarith
    field_simp
    <;> ring
  · intro a b h t
    have hd := (gap_pos h t).ne'
    field_simp
    <;> ring
  · intro a b h t; ring
