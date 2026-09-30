-- Prove2me | solution 1 for lean_workbook_plus_16728
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:55:54.261366+00:00
-- url     : https://prove2.me/submissions/efd1c190-69f9-4050-a280-a85f81006ae2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem solution (f : ℝ → ℝ) :
    (∀ x y, f (x ^ 2 - y ^ 2) = (x - y) * (f x + f y)) ↔
      ∃ a : ℝ, ∀ x, f x = a * x := by
  constructor
  · intro hf
    have h0 : f 0 = 0 := by simpa using hf 0 0
    have hn := hf (-1) 0
    norm_num [h0] at hn
    have hneg : f (-1) = -f 1 := by linarith! only [hn]
    refine ⟨f 1, ?_⟩
    intro x
    have hp := hf x 1
    have hm := hf x (-1)
    norm_num at hp hm
    rw [hneg] at hm
    nlinarith! only [hp, hm]
  · rintro ⟨a, ha⟩ x y
    simp only [ha]
    ring
