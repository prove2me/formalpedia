-- Prove2me | Theorems.Thm_lean_workbook_plus_39610
-- name    : lean_workbook_plus_39610
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/cbfb78a8-9912-4b0c-9746-0ec8f36ea2a8
-- statement:
--   Prove the following inequality: $\frac{a^2+3bc}{(b+c)^2}+\frac{b^2+3ca}{(c+a)^2}+\frac{c^2+3ab}{(a+b)^2}+\frac{13}{12} \ge \frac{49}{4}\cdot \frac{ab+bc+ca}{(a+b+c)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39610 : ∀ a b c : ℝ, (a^2 + 3 * b * c) / (b + c)^2 + (b^2 + 3 * c * a) / (c + a)^2 + (c^2 + 3 * a * b) / (a + b)^2 + 13 / 12 ≥ (49 / 4) * (a * b + b * c + c * a) / (a + b + c)^2   :=  by sorry
