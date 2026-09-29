-- Prove2me | Theorems.Thm_lean_workbook_plus_50021
-- name    : lean_workbook_plus_50021
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/55609f22-ca74-4489-a2eb-7b13cb6a6aa7
-- statement:
--   Let a,b,c,d>0 such that $ ac+bd=2. $ Prove that $ (ad-bc)^2 + 2\ge ad+bc $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50021 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a * c + b * d = 2) : (a * d - b * c) ^ 2 + 2 ≥ a * d + b * c   :=  by sorry
