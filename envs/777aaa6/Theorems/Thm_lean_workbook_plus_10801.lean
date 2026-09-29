-- Prove2me | Theorems.Thm_lean_workbook_plus_10801
-- name    : lean_workbook_plus_10801
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/bdfca74a-f8f4-48fa-9b67-082f378f16f0
-- statement:
--   Prove that if $ a, b, c$ and $d$ are real numbers, then \n $$a + b+ c + d - a^2 -b^2 -c^2 - d^2 \leq1 .$$ (21st Transylvanian Hungarian Mathematical Competition, 2011)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10801 (a b c d : ℝ) : a + b + c + d - a ^ 2 - b ^ 2 - c ^ 2 - d ^ 2 ≤ 1   :=  by sorry
