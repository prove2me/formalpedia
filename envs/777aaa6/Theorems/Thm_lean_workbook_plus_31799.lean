-- Prove2me | Theorems.Thm_lean_workbook_plus_31799
-- name    : lean_workbook_plus_31799
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/449d37a4-4669-4533-9a75-14557f4a6985
-- statement:
--   Prove that $a^3+b^3+c^3+1\ge 4(abc)^3$ given $a,b,c > 0$ and $ab+ac+bc = 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31799 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : a ^ 3 + b ^ 3 + c ^ 3 + 1 ≥ 4 * (a * b * c) ^ 3   :=  by sorry
