-- Prove2me | Theorems.Thm_lean_workbook_plus_49052
-- name    : lean_workbook_plus_49052
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/be03a20e-2c9c-4182-a6c5-dc9cb58bfa88
-- statement:
--   Prove that $a^2b^2+a^2c^2+b^2c^2\ge a^2bc+b^2ac+c^2ab$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49052 (a b c : ℝ) : a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2 ≥ a ^ 2 * b * c + b ^ 2 * a * c + c ^ 2 * a * b   :=  by sorry
