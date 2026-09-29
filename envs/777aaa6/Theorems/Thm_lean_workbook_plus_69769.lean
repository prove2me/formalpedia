-- Prove2me | Theorems.Thm_lean_workbook_plus_69769
-- name    : lean_workbook_plus_69769
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/dbee8daf-3b38-4bc9-a79d-cdca0c26fe04
-- statement:
--   If $a^2+1$ is divisible by $23$, then prove that $a^{22}+1$ is also divisible by $23$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69769 (a : ℤ) (h : 23 ∣ a^2 + 1) : 23 ∣ a^22 + 1   :=  by sorry
