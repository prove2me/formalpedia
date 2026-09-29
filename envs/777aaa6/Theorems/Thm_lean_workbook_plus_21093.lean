-- Prove2me | Theorems.Thm_lean_workbook_plus_21093
-- name    : lean_workbook_plus_21093
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/ff234fb9-2990-41cf-9efd-a9c56f690ad4
-- statement:
--   $\Longleftrightarrow (a+b+c)^2\ge 3(ab+bc+ca)\Longleftrightarrow \frac{2(a+b+c)^2}{a^2 + b^2 + c^2}\ge\frac{6(ab+bc+ca)}{a^2 + b^2 + c^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21093 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) ↔ 2 * (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 6 * (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
