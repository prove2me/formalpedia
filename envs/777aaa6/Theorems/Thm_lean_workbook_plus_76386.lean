-- Prove2me | Theorems.Thm_lean_workbook_plus_76386
-- name    : lean_workbook_plus_76386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/47b909c6-6c84-4c4b-92e7-736f3d3cf508
-- statement:
--   If $a,b,c$ be even, then $a^2+b^2+c^2$ is divisible by $4.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76386 (a b c : ℤ) (h : Even a ∧ Even b ∧ Even c): 4 ∣ a ^ 2 + b ^ 2 + c ^ 2   :=  by sorry
