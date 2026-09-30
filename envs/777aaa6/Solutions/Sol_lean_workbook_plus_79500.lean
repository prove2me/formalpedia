-- Prove2me | solution 1 for lean_workbook_plus_79500
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:47.484147+00:00
-- url     : https://prove2.me/submissions/5e626902-98c9-4a68-8eb3-5348fc60bd74

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ) :
    a > 0 ∧ b > 0 ∧ c > 0 ∧ x > 0 ∧ y > 0 ∧ z > 0 →
    (a * x + b * y + c * z = x * y * z ↔
      a / y / z + b / x / z + c / x / y = 1) := by
  rintro ⟨ha, hb, hc, hx, hy, hz⟩
  field_simp
  <;> constructor <;> intro h <;> nlinarith
