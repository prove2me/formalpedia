-- Prove2me | solution 2 for lean_workbook_plus_76741
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:38:19.109972+00:00
-- url     : https://prove2.me/submissions/770bf823-cad3-4bc6-896a-a5841b481076

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

private theorem full_bounds (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 2*a+b ≤ 3) :
    (-3 ≤ a-b+a*b ∧ a-b+a*b ≤ 3/2) ∧
    (-6 ≤ a-2*b+3*a*b ∧ a-2*b+3*a*b ≤ 13/6) := by
  have hb3 : b ≤ 3 := by linarith only [ha, hs]
  have hab : 0 ≤ a*b := mul_nonneg ha hb
  have hslack : 0 ≤ 3-2*a-b := by linarith only [hs]
  constructor
  · constructor
    · nlinarith only [ha, hb3, hab]
    · by_cases ha1 : a ≤ 1
      · have h := mul_nonneg (sub_nonneg.mpr ha1) hb
        nlinarith only [h, ha1]
      · have h := mul_nonneg (show 0 ≤ a-1 by linarith only [ha1]) hslack
        nlinarith only [h, sq_nonneg (a-(3/2:ℝ))]
  · constructor
    · nlinarith only [ha, hb3, hab]
    · by_cases ha2 : 3*a ≤ 2
      · have h := mul_nonneg (show 0 ≤ 2-3*a by linarith only [ha2]) hb
        nlinarith only [h, ha2]
      · have h := mul_nonneg (show 0 ≤ 3*a-2 by linarith only [ha2]) hslack
        nlinarith only [h, sq_nonneg (a-(7/6:ℝ))]

theorem solution (a b : ℝ) (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) (h₃ : 2*a+b ≤ 3) :
    -3 ≤ a-b+a*b ∧ a-b+a*b ≤ 3/2 := by
  exact (full_bounds a b h₁ h₂ h₃).1
