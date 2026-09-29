-- Prove2me | Theorems.Thm_lean_workbook_plus_32492
-- name    : lean_workbook_plus_32492
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/ab6533c9-9d97-43d8-a357-b86cc97c4629
-- statement:
--   Let a and b be positive integers such that $a + ab = 1443$ and $ab + b = 1444$ . Find $10a + b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32492 (a b : ℕ) (h1 : a + a * b = 1443) (h2 : a * b + b = 1444) : 10 * a + b = 408   :=  by sorry
