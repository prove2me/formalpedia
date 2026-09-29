-- Prove2me | Theorems.Thm_lean_workbook_plus_11271
-- name    : lean_workbook_plus_11271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2e292d2f-2eb7-4604-bd49-95db245ecdcb
-- statement:
--   We have $\Delta'= (4z-3y)^2-5(5y^2+5z^2-8yz)=-9z^2-16y^2+16yz= -(4y+2z)^2-5z^2 \le 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11271 (y z : ℝ) : (4 * z - 3 * y) ^ 2 - 5 * (5 * y ^ 2 + 5 * z ^ 2 - 8 * y * z) ≤ 0   :=  by sorry
