-- Prove2me | Theorems.Thm_lean_workbook_plus_9368
-- name    : lean_workbook_plus_9368
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/5e164ab1-9b32-4ad0-abdb-3fca6c6eaa45
-- statement:
--   Prove that $\frac{(ab+bc+ca)^2}{a+b+c+3} \geq \frac{3}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9368 : ∀ a b c : ℝ, (a * b + b * c + c * a)^2 / (a + b + c + 3) ≥ 3 / 2   :=  by sorry
