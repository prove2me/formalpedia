-- Prove2me | Theorems.Thm_lean_workbook_plus_19289
-- name    : lean_workbook_plus_19289
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/73e759b6-7a26-4ceb-b5e6-6e630e6204c3
-- statement:
--   Prove $a^2b+b^2c+c^2a\le \sqrt{(a^2+b^2+c^2).\frac{(a^2+b^2+c^2)^2}{3}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19289 (a b c : ℝ) : a^2 * b + b^2 * c + c^2 * a ≤ Real.sqrt ((a^2 + b^2 + c^2) * (a^2 + b^2 + c^2)^2 / 3)   :=  by sorry
