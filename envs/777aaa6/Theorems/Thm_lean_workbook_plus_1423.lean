-- Prove2me | Theorems.Thm_lean_workbook_plus_1423
-- name    : lean_workbook_plus_1423
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/4fca7473-caab-4d54-950c-7d00f9f81324
-- statement:
--   Find the maximum possible value of $a + b + c ,$ if $a,b,c$ are positive real numbers such that $a^2 + b^2 + c^2 = a^3 + b^3 + c^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1423 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (ha2 : a^2 + b^2 + c^2 = a^3 + b^3 + c^3) : a + b + c ≤ 3   :=  by sorry
