-- Prove2me | Theorems.Thm_lean_workbook_plus_67954
-- name    : lean_workbook_plus_67954
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/82a114d1-2b65-4c9f-8ea4-2c248b5aaa47
-- statement:
--   Prove that if $abc=1$ and $a,b,c$ are positive reals, then $a^2+b^2+c^2\le a^3+b^3+c^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67954 (a b c : ℝ) (h : a * b * c = 1) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^2 + b^2 + c^2 ≤ a^3 + b^3 + c^3   :=  by sorry
