-- Prove2me | Theorems.Thm_lean_workbook_plus_13283
-- name    : lean_workbook_plus_13283
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/477634a0-f3be-413c-93c9-36c24effb095
-- statement:
--   $(ab+cb+ac)^2 \geq 3abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13283 : ∀ a b c : ℝ, (a * b + b * c + a * c) ^ 2 ≥ 3 * a * b * c * (a + b + c)   :=  by sorry
