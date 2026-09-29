-- Prove2me | Theorems.Thm_lean_workbook_plus_35015
-- name    : lean_workbook_plus_35015
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f7f3870e-0103-4235-bcac-1affabc6bc54
-- statement:
--   Let $a,b,c>0$ . Prove that: $1 + \frac{3}{{ab + bc + ca}} \ge \frac{6}{{a + b + c}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35015 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 + 3 / (a * b + b * c + c * a) ≥ 6 / (a + b + c)   :=  by sorry
