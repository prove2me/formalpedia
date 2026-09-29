-- Prove2me | Theorems.Thm_lean_workbook_plus_79087
-- name    : lean_workbook_plus_79087
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/8def07ad-6f32-437f-985e-2d796626e18d
-- statement:
--   Given that $mn$ is even, prove that one of $m$ or $n$ must be even.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79087 {m n : ℤ} (h : Even (m * n)) : Even m ∨ Even n   :=  by sorry
