-- Prove2me | Theorems.Thm_lean_workbook_plus_12686
-- name    : lean_workbook_plus_12686
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f11eaee6-4692-4ac6-aff8-da1876f406ec
-- statement:
--   Prove $a^3+b^3+c^3\ge a^2b+b^2c+c^2a$ for all non-negative real numbers $a,b,c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12686 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a ^ 3 + b ^ 3 + c ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * a   :=  by sorry
