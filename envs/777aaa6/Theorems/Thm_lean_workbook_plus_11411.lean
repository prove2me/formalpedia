-- Prove2me | Theorems.Thm_lean_workbook_plus_11411
-- name    : lean_workbook_plus_11411
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/06dfa96c-f987-4f19-9b53-484550ae8d92
-- statement:
--   Prove the inequality: $a^2b^2 + b^2c^2 + a^2c^2 - ab^2c - abc^2 - a^2bc \ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11411 : ∀ a b c : ℝ, a^2 * b^2 + b^2 * c^2 + a^2 * c^2 - a * b^2 * c - a * b * c^2 - a^2 * b * c ≥ 0   :=  by sorry
