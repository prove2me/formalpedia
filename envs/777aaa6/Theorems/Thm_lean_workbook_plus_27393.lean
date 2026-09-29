-- Prove2me | Theorems.Thm_lean_workbook_plus_27393
-- name    : lean_workbook_plus_27393
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/8ec0ac0d-bc8d-42a5-8026-13332fb5e16a
-- statement:
--   (c) If $ x \neq 0$ and $ xy = 1$ then $ y = 1/x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27393 (x y : ℝ) (h₀ : x ≠ 0) (h₁ : x * y = 1) : y = 1 / x   :=  by sorry
