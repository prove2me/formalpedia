-- Prove2me | Theorems.Thm_lean_workbook_plus_74222
-- name    : lean_workbook_plus_74222
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/27b207df-edb7-4283-af11-592e2d60a8ac
-- statement:
--   Let $r_1$ , $r_2$ , $r_3$ be the distinct real roots of $x^3-2019x^2-2020x+2021=0$ . Prove that $r_1^3+r_2^3+r_3^3$ is an integer multiple of $3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74222 (r₁ r₂ r₃ : ℝ) (h₁ : r₁ ≠ r₂) (h₂ : r₁ ≠ r₃) (h₃ : r₂ ≠ r₃) (hr : r₁^3 - 2019 * r₁^2 - 2020 * r₁ + 2021 = 0 ∧ r₂^3 - 2019 * r₂^2 - 2020 * r₂ + 2021 = 0 ∧ r₃^3 - 2019 * r₃^2 - 2020 * r₃ + 2021 = 0) : 3 ∣ r₁^3 + r₂^3 + r₃^3   :=  by sorry
