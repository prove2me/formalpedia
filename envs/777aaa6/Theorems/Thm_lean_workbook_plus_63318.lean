-- Prove2me | Theorems.Thm_lean_workbook_plus_63318
-- name    : lean_workbook_plus_63318
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/441896ba-8550-410b-a63d-1f86a6e70919
-- statement:
--   Use the Principal of Mathematical Induction to prove that $(n+1)(n+2)(n+3)$ is divisible by $6$ for all positive integers $n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63318 (n : ℕ) : 6 ∣ (n + 1) * (n + 2) * (n + 3)   :=  by sorry
