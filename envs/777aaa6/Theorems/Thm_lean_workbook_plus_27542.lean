-- Prove2me | Theorems.Thm_lean_workbook_plus_27542
-- name    : lean_workbook_plus_27542
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/a4361703-62e3-4f27-9182-76ca4f6bbcac
-- statement:
--   If $ a + b + c = 5$ and $ ab + bc + ac = 3$ prove that $ - 1\leq c\leq \frac {13}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27542 (a b c : ℝ) (h1 : a + b + c = 5) (h2 : a * b + b * c + a * c = 3) : -1 ≤ c ∧ c ≤ 13 / 3   :=  by sorry
