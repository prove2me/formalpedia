-- Prove2me | Theorems.Thm_lean_workbook_plus_40405
-- name    : lean_workbook_plus_40405
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/c2999958-e99a-4bba-941b-ab7e25ff76a0
-- statement:
--   Prove that for any natural number $n \geq 6$ , then $$(n+3)^3 \leq 3^n$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40405 (n : ℕ) (hn : 6 ≤ n) : (n + 3)^3 ≤ 3^n   :=  by sorry
