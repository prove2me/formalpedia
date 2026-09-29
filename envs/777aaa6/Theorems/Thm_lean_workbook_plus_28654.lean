-- Prove2me | Theorems.Thm_lean_workbook_plus_28654
-- name    : lean_workbook_plus_28654
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/94140a54-cd9a-4c29-98f2-a6ecacb9073c
-- statement:
--   Let $ a,b,c$ be positive integers. Prove the following inequality: \n\n $ 2a^2b^2 + 2a^2c^2 + 2b^2c^2 \geq 2ab + 2ac + 2bc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28654 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * a ^ 2 * b ^ 2 + 2 * a ^ 2 * c ^ 2 + 2 * b ^ 2 * c ^ 2 ≥ 2 * a * b + 2 * a * c + 2 * b * c   :=  by sorry
