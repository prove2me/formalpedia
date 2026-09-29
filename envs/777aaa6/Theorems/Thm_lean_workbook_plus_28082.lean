-- Prove2me | Theorems.Thm_lean_workbook_plus_28082
-- name    : lean_workbook_plus_28082
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3ee30d82-0e0c-4437-9437-6c8fc8df05ba
-- statement:
--   Prove that $3(a+b+c)^2 \ge a^2+b^2+c^2+8(ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28082 (a b c : ℝ) : 3 * (a + b + c) ^ 2 ≥ a ^ 2 + b ^ 2 + c ^ 2 + 8 * (a * b + b * c + c * a)   :=  by sorry
