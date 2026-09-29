-- Prove2me | Theorems.Thm_lean_workbook_plus_35981
-- name    : lean_workbook_plus_35981
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d347a963-26ee-4fbf-b4d1-ae01824c6f98
-- statement:
--   Show that $ a^6 + b^6 + c^6 - 6abc \geq 3(abc - 1)^2 - 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35981 (a b c : ℝ) : a ^ 6 + b ^ 6 + c ^ 6 - 6 * a * b * c ≥ 3 * (a * b * c - 1) ^ 2 - 3   :=  by sorry
