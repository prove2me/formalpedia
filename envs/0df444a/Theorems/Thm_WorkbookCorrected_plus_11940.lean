-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_11940
-- name    : WorkbookCorrected.plus_11940
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:16:57.162585+00:00
-- url     : https://prove2.me/theorems/47bfe535-f7d9-413e-be87-6c3be1b5116b
-- title:
--   Boundedness from a quadratic inequality between adjacent sequence terms
-- statement:
--   Let $(x_n)_{n\ge1}$ be a sequence of real numbers which satisfies the following relation: $(x_{n+1}-x_n)(x_{n+1}+x_n+1)\le0$. Show that $(x_n)_{n\ge1}$ is bounded
--
--   Formalization Note: The source sequence starts at n=1. This correction restricts both the relation and the boundedness conclusion to the stated positive indices, leaving an unused index0 unconstrained.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_11940 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_11940; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_11940 (x : ℕ → ℝ)
    (h : ∀ n : ℕ, 1≤n → (x (n+1)-x n)*(x (n+1)+x n+1) ≤ 0) :
    ∃ M : ℝ, ∀ n : ℕ, 1≤n → |x n| ≤ M := by sorry
