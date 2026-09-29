-- Prove2me | Theorems.Thm_lean_workbook_plus_69597
-- name    : lean_workbook_plus_69597
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/6f7cbd24-ba8d-4883-af12-35403d84ba8f
-- statement:
--   Prove the inequality $\sqrt{k+1} \leq 1 + \frac{k}{\sqrt{k} + 1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69597 (k : ℕ) : Real.sqrt (k + 1) ≤ 1 + k / (Real.sqrt k + 1)   :=  by sorry
