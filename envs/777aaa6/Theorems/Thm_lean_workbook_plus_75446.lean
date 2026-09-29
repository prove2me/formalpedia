-- Prove2me | Theorems.Thm_lean_workbook_plus_75446
-- name    : lean_workbook_plus_75446
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/04960eea-a065-4632-9781-e4ee5fb8a208
-- statement:
--   For $a, b, c>0$ prove: $a^3+b^3+c^3\ge \frac{1}{3}(a^2+b^2+c^2)(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75446 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 + b^3 + c^3 ≥ (1/3) * (a^2 + b^2 + c^2) * (a + b + c)   :=  by sorry
