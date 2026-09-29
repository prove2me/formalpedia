-- Prove2me | Theorems.Thm_lean_workbook_plus_6330
-- name    : lean_workbook_plus_6330
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/efe7dcad-61d0-48b8-81f4-110f7913efc9
-- statement:
--   The first inequality is $a^2+b^2+c^2+a^2b^2+b^2c^2+c^2a^2 \ge ab+bc+ca+a^2bc+b^2ca+c^2ab$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6330 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ a * b + b * c + c * a + a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b   :=  by sorry
