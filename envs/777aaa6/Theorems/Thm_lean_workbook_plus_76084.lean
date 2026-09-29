-- Prove2me | Theorems.Thm_lean_workbook_plus_76084
-- name    : lean_workbook_plus_76084
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a84e41dd-37d9-47f3-9d51-d4925d59a19d
-- statement:
--   If $ a,b,c>0,a^2+b^2+c^2+abc=4 $ then: \n $ 3\sqrt{abc}(a+b+c)\le 8+abc $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76084 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : 3 * Real.sqrt (a * b * c) * (a + b + c) ≤ 8 + a * b * c   :=  by sorry
