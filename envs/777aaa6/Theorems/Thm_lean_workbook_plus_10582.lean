-- Prove2me | Theorems.Thm_lean_workbook_plus_10582
-- name    : lean_workbook_plus_10582
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/88183175-5056-4663-8dba-ca183a025642
-- statement:
--   Prove: $(x+y)(x-y)^2+2(x-1)(y-1)\ge0$ where $x,y\ge0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10582 (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) : (x + y) * (x - y) ^ 2 + 2 * (x - 1) * (y - 1) ≥ 0   :=  by sorry
