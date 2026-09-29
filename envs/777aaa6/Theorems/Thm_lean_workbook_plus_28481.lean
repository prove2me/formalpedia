-- Prove2me | Theorems.Thm_lean_workbook_plus_28481
-- name    : lean_workbook_plus_28481
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/971ac89d-55a3-49ab-a810-3aa71ba34568
-- statement:
--   Let $a,b>0$ Prove that:\n $\frac{2ab}{a^{2}+4b^{2}}+\frac{b^{2}}{3a^{2}+2b^{2}}\leq \frac{3}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28481 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (2 * a * b / (a ^ 2 + 4 * b ^ 2) + b ^ 2 / (3 * a ^ 2 + 2 * b ^ 2)) ≤ 3 / 5   :=  by sorry
