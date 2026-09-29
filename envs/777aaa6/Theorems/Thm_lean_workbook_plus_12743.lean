-- Prove2me | Theorems.Thm_lean_workbook_plus_12743
-- name    : lean_workbook_plus_12743
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/9d623868-8099-47dc-b36d-fa5e921162f4
-- statement:
--   $ 2(a + b + c)^2\leq{3(a^2 + b^2 + c^2 + ab + bc + ca)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12743 : ∀ a b c : ℝ, 2 * (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a)   :=  by sorry
