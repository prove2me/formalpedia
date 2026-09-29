-- Prove2me | Theorems.Thm_lean_workbook_plus_60976
-- name    : lean_workbook_plus_60976
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/e755214b-a34f-4a9b-81bb-05238c111cb0
-- statement:
--   Prove that $17 \nmid n^4+8$ for all positive integers $n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60976 : ∀ n : ℕ, ¬ 17 ∣ n^4 + 8   :=  by sorry
