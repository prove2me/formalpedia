-- Prove2me | Theorems.Thm_lean_workbook_plus_35946
-- name    : lean_workbook_plus_35946
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/dbeb801b-26c8-44ae-b5f1-f1d9a6496863
-- statement:
--   For #1 \nIndeed，the inequality is also true for any real numbers $a,b$ and $c$ . \nBecause of $(a^2+b^2+c^2)^3-3(a^2b+b^2c+c^2a)^2=2\sum{a^2c^2(a-b)^2}+\sum{(ab^2-c^3)^2}\ge{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35946 (a b c : ℝ) : (a^2 + b^2 + c^2)^3 ≥ 3 * (a^2 * b + b^2 * c + c^2 * a)^2   :=  by sorry
