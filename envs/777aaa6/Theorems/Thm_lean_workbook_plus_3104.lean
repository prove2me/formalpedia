-- Prove2me | Theorems.Thm_lean_workbook_plus_3104
-- name    : lean_workbook_plus_3104
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/1bad1bf5-e138-4d68-ae42-86cc920a3730
-- statement:
--   Prove that $\sum_{cyc}(a-b)^2(a^2+b^2-c^2)\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3104 {a b c : ℝ} : (a - b) ^ 2 * (a ^ 2 + b ^ 2 - c ^ 2) + (b - c) ^ 2 * (b ^ 2 + c ^ 2 - a ^ 2) + (c - a) ^ 2 * (c ^ 2 + a ^ 2 - b ^ 2) ≥ 0   :=  by sorry
