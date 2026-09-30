-- Prove2me | solution 1 for lean_workbook_plus_26494
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:02:01.726187+00:00
-- url     : https://prove2.me/submissions/88ed74be-ccd2-412c-872e-f819ef97faa4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

lemma cube_product_bound (p q r : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hq : q ∈ Set.Icc 0 1) (hr : r ∈ Set.Icc 0 1) : p * q * r ≤ p := by
  calc
    p * q * r ≤ p * q * 1 :=
      mul_le_mul_of_nonneg_left hr.2 (mul_nonneg hp.1 hq.1)
    _ ≤ p * 1 := by simpa using mul_le_mul_of_nonneg_left hq.2 hp.1
    _ = p := mul_one p

theorem solution (x y z : ℝ) (hx : x ∈ Set.Icc 0 (1 / 2))
    (hy : y ∈ Set.Icc 0 (1 / 2)) (hz : z ∈ Set.Icc 0 (1 / 2)) :
    (2 / 3) * (x + y + z) ≥ (y + x) * (y + z) * (z + x) := by
  have hp : y + x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  have hq : y + z ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hy.1, hz.1], by linarith [hy.2, hz.2]⟩
  have hr : z + x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hz.1, hx.1], by linarith [hz.2, hx.2]⟩
  nlinarith [cube_product_bound (y + x) (y + z) (z + x) hp hq hr,
    cube_product_bound (y + z) (z + x) (y + x) hq hr hp,
    cube_product_bound (z + x) (y + x) (y + z) hr hp hq]
