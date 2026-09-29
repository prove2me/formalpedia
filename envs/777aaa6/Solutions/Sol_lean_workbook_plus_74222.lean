-- Prove2me | solution 1 for lean_workbook_plus_74222
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:51:48.157225+00:00
-- url     : https://prove2.me/submissions/7e432bf7-1cf1-43b6-a876-1a998f11548a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (r₁ r₂ r₃ : ℝ) (h₁ : r₁ ≠ r₂) (h₂ : r₁ ≠ r₃) (h₃ : r₂ ≠ r₃) (hr : r₁^3 - 2019 * r₁^2 - 2020 * r₁ + 2021 = 0 ∧ r₂^3 - 2019 * r₂^2 - 2020 * r₂ + 2021 = 0 ∧ r₃^3 - 2019 * r₃^2 - 2020 * r₃ + 2021 = 0) : 3 ∣ r₁^3 + r₂^3 + r₃^3 := by
  norm_num
