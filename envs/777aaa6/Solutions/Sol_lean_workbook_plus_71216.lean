-- Prove2me | solution 1 for lean_workbook_plus_71216
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:56.232276+00:00
-- url     : https://prove2.me/submissions/23ebbc1f-ad33-4ea0-b058-f60dd88992e4

import Mathlib

theorem solution (a b c : ℝ)
    (h₀ : ∀ x ∈ Set.Icc (-1) 1, abs (a * x ^ 2 + b * x + c) ≤ 1) :
    abs a + abs b + abs c ≤ 4 := by
  have hn : abs (a - b + c) ≤ 1 := by
    convert h₀ (-1) (by constructor <;> norm_num) using 1 <;> ring_nf
  have hz : abs c ≤ 1 := by simpa using h₀ 0 (by constructor <;> norm_num)
  have hp : abs (a + b + c) ≤ 1 := by simpa using h₀ 1 (by constructor <;> norm_num)
  rcases abs_le.mp hz with ⟨hc0, hc1⟩
  rcases abs_le.mp hn with ⟨hn0, hn1⟩
  rcases abs_le.mp hp with ⟨hp0, hp1⟩
  have ha : abs a ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : abs b ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

#print axioms solution
