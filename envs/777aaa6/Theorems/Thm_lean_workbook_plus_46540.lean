-- Prove2me | Theorems.Thm_lean_workbook_plus_46540
-- name    : lean_workbook_plus_46540
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/61f55603-02ab-40ab-818b-72994e345dad
-- statement:
--   prove that $ n(n+1)/2$ is always an integer for all integer values of $ n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46540 (n : ℤ) : ∃ k : ℤ, n * (n + 1) / 2 = k   :=  by sorry
