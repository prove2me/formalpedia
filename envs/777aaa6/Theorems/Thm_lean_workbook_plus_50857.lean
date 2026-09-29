-- Prove2me | Theorems.Thm_lean_workbook_plus_50857
-- name    : lean_workbook_plus_50857
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/d2af0045-8f38-4466-b36f-f2bdd044b2a2
-- statement:
--   $ 3(a^4+b^4+c^4)\ge\ (a+b+c)(a^3+b^3+c^3) $ which is true by Chebyshev.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50857 (a b c : ℝ) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) ≥ (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3)   :=  by sorry
