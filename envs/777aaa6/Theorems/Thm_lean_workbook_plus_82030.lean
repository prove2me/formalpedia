-- Prove2me | Theorems.Thm_lean_workbook_plus_82030
-- name    : lean_workbook_plus_82030
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/f0d08a1b-53f1-4716-8723-591c51f142ee
-- statement:
--   Prove $ (a+b+c)(\frac{a^2}{b}+ \frac{b^2}{c}+ \frac{c^2}{a}) \ge 3(a^2+b^2+c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82030 : ∀ a b c : ℝ, (a + b + c) * (a^2 / b + b^2 / c + c^2 / a) ≥ 3 * (a^2 + b^2 + c^2)   :=  by sorry
