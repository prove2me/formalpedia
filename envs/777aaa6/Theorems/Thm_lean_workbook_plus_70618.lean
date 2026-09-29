-- Prove2me | Theorems.Thm_lean_workbook_plus_70618
-- name    : lean_workbook_plus_70618
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/75331f2e-7a19-43ab-a80e-57855a3ddb0c
-- statement:
--   $(a+b+c)^{2}\geq 2(ab+bc+ca)+a^{2}+b^{2}+c^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70618 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 2 * (a * b + b * c + c * a) + a ^ 2 + b ^ 2 + c ^ 2   :=  by sorry
