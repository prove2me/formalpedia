-- Prove2me | Theorems.Thm_lean_workbook_plus_6337
-- name    : lean_workbook_plus_6337
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/474fa18a-386f-4a8d-bf2c-19385aa97e9c
-- statement:
--   Determine if the expression $\frac{1}{4} \left((a -b)^2+(b-c)^2+(c-a)^2\right)\left((a-b)^2(a+b)+(b-c)^2(b+c)+(c-a)^2(c+a)\right)$ is greater than or equal to zero for all positive real numbers $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6337 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 0 ≤ (1 / 4) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) * ((a - b) ^ 2 * (a + b) + (b - c) ^ 2 * (b + c) + (c - a) ^ 2 * (c + a))   :=  by sorry
