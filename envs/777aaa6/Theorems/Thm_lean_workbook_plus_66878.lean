-- Prove2me | Theorems.Thm_lean_workbook_plus_66878
-- name    : lean_workbook_plus_66878
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/3b34ff07-ced8-4faa-aa89-19b8310193e0
-- statement:
--   Prove that $x^2 + \dfrac 1{4x} \ge \dfrac{3}{4}$ for $x > 0$ using the Arithmetic Mean-Geometric Mean (AM-GM) inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66878 (x : ℝ) (hx : x > 0) : x^2 + 1 / (4 * x) ≥ 3 / 4   :=  by sorry
