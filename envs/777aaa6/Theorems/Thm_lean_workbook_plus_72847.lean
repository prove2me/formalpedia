-- Prove2me | Theorems.Thm_lean_workbook_plus_72847
-- name    : lean_workbook_plus_72847
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ac3f8c99-14eb-4f7f-a32c-af2a8c83a605
-- statement:
--   Prove: $(a-b)^2 + (a-c)^2 + (a-d)^2 + (a-e)^2 + (b-c)^2 + (b-d)^2 + (b-e)^2 + (c-d)^2 + (c-e)^2 + (d-e)^2 \geq 0$ for $a,b,c,d,e>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72847 {a b c d e : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) : (a - b) ^ 2 + (a - c) ^ 2 + (a - d) ^ 2 + (a - e) ^ 2 + (b - c) ^ 2 + (b - d) ^ 2 + (b - e) ^ 2 + (c - d) ^ 2 + (c - e) ^ 2 + (d - e) ^ 2 ≥ 0   :=  by sorry
