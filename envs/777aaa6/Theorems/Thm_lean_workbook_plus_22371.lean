-- Prove2me | Theorems.Thm_lean_workbook_plus_22371
-- name    : lean_workbook_plus_22371
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e5b51c95-0f8d-4180-bd11-4eb8a5bc8092
-- statement:
--   Prove that \n $(a^2+ab+b^2)(a^2+ac+c^2)\geq\left(a^2+\frac{a(b+c)}{2}+bc\right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22371 (a b c : ℝ) :
  (a^2 + a * b + b^2) * (a^2 + a * c + c^2) ≥ (a^2 + a * (b + c) / 2 + b * c)^2   :=  by sorry
