-- Prove2me | Theorems.Thm_lean_workbook_plus_32551
-- name    : lean_workbook_plus_32551
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/10da130d-ad3a-48a9-bcd6-57b771a25507
-- statement:
--   prove that $ \sqrt{2}$ is an irrational number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32551 : ¬ ∃ a b : ℕ, (a : ℝ) / b = Real.sqrt 2   :=  by sorry
