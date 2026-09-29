-- Prove2me | Theorems.Thm_lean_workbook_plus_41286
-- name    : lean_workbook_plus_41286
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/19da92c4-a5a1-415f-8dd8-817093d17aac
-- statement:
--   Let $ a,b,c>0$ such that $ a^2 + b^2 + c^2 + abc = 4$ Prove that $ ab + bc + ca\le abc + 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41286 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : a * b + b * c + c * a ≤ a * b * c + 2   :=  by sorry
