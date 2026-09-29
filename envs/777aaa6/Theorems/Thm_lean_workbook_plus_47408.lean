-- Prove2me | Theorems.Thm_lean_workbook_plus_47408
-- name    : lean_workbook_plus_47408
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/27b71dd7-af28-46d0-90fd-adfd18b4fded
-- statement:
--   Prove that there exists two positive constants $C_{1}$ and $C_{2}$ such that $C_{1}\sqrt{n} (\frac{n}{e})^{n} < n! < C_{2}\sqrt{n}(\frac{n}{e})^{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47408 : ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧ ∀ n : ℕ, C1 * Real.sqrt n * (n/e)^n < n! ∧ n! < C2 * Real.sqrt n * (n/e)^n   :=  by sorry
