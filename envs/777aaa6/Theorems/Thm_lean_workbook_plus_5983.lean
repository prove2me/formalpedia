-- Prove2me | Theorems.Thm_lean_workbook_plus_5983
-- name    : lean_workbook_plus_5983
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/bda98efa-77d9-4a33-bfbd-fd68b90e04af
-- statement:
--   If $ a,b,c>0 $ prove that:\n $2\sqrt{(a^2b+b^2c+c^2a)(a+b+c)}\ge 2(ab+bc+ca) $\n\n__________\n\nMarin Sandu
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5983 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * Real.sqrt ((a^2 * b + b^2 * c + c^2 * a) * (a + b + c)) ≥ 2 * (a * b + b * c + c * a)   :=  by sorry
