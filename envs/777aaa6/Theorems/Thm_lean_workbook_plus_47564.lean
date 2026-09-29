-- Prove2me | Theorems.Thm_lean_workbook_plus_47564
-- name    : lean_workbook_plus_47564
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/6404542c-dbb6-40c4-83ab-52e2df7b8019
-- statement:
--   Let $ a,b,c > 0$ be such that $ a + b + c = 1$ . Prove the followings: (3) $ a^2(b + c) + b^2(c + a) + c^2(a + b) \ge 6abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47564 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) ≥ 6 * a * b * c   :=  by sorry
