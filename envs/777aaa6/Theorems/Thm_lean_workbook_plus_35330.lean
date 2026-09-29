-- Prove2me | Theorems.Thm_lean_workbook_plus_35330
-- name    : lean_workbook_plus_35330
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/e8574498-61f4-4ca7-a65b-7f2ab97850f5
-- statement:
--   For 4 positive real numbers $a, b, c$ and $d$ show that\n\n $$\frac{ab + bc + cd + ad}{a^2+b^2+c^2+d^2}\leq1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35330 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a * b + b * c + c * d + a * d) / (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ≤ 1   :=  by sorry
