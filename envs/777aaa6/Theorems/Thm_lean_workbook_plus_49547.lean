-- Prove2me | Theorems.Thm_lean_workbook_plus_49547
-- name    : lean_workbook_plus_49547
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/d47096ed-19a3-422f-b354-78b6bcd529a2
-- statement:
--   $\frac{r+s+t}{3} \geq \sqrt[3]{rst} \implies r+s+t \geq 3\sqrt[3]{rst}$ , and
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49547 (r s t : ℝ) : (r + s + t) / 3 ≥ (r * s * t)^(1/3) → r + s + t ≥ 3 * (r * s * t)^(1/3)   :=  by sorry
