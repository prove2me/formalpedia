-- Prove2me | Theorems.Thm_lean_workbook_plus_79890
-- name    : lean_workbook_plus_79890
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/34a54c4b-2249-4fbb-a0a9-95c0154da3fd
-- statement:
--   Prove that $\frac{ab}{c^{2}}+\frac{ac}{b^{2}}+\frac{bc}{a^{2}}+\frac{a^{2}}{bc}+\frac{b^{2}}{ac}+\frac{c^{2}}{ab}-6\ge0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79890 : ∀ a b c : ℝ, (a * b / c ^ 2 + a * c / b ^ 2 + b * c / a ^ 2 + a ^ 2 / (b * c) + b ^ 2 / (a * c) + c ^ 2 / (a * b) - 6) ≥ 0   :=  by sorry
