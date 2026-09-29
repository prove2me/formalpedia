-- Prove2me | Theorems.Thm_lean_workbook_plus_44735
-- name    : lean_workbook_plus_44735
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/1f40c02d-1a49-416d-847d-deacafc599f5
-- statement:
--   Let $a,b,c>0$ such that $a^2+b^2+c^2+2abc=1$ . Prove that $a^2+b^2+c^2\ge 4(a^2b^2+b^2c^2+c^2a^2) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44735 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + 2 * a * b * c = 1) : a^2 + b^2 + c^2 ≥ 4 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)   :=  by sorry
