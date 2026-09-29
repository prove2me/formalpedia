-- Prove2me | Theorems.Thm_lean_workbook_plus_24464
-- name    : lean_workbook_plus_24464
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/ab41b250-8562-4594-839f-94573ebe7290
-- statement:
--   $p^2=(2k-p)^2-4a^2=(2k-p-2a)(2k-p+2a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24464 (p a : ℤ) (h : p^2 = (2 * k - p)^2 - 4 * a^2): ∃ k : ℤ, p^2 = (2 * k - p - 2 * a) * (2 * k - p + 2 * a)   :=  by sorry
