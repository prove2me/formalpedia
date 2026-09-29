-- Prove2me | Theorems.Thm_lean_workbook_plus_45770
-- name    : lean_workbook_plus_45770
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/3cb04af4-1b52-4ff5-8fc9-65c0d4237997
-- statement:
--   Let $ x\ ,\ y\in R$ such that $ 0 < y\le x\le 2\ ,\ xy^2 \le 2$ . Prove that $ x + 2y\le 4$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45770 (x y : ℝ) (h₁ : 0 < y ∧ y ≤ x ∧ x ≤ 2) (h₂ : x * y ^ 2 ≤ 2) : x + 2 * y ≤ 4   :=  by sorry
