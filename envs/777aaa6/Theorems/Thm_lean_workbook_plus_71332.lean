-- Prove2me | Theorems.Thm_lean_workbook_plus_71332
-- name    : lean_workbook_plus_71332
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7379cce9-64fa-4d79-844c-c95dd4ce440c
-- statement:
--   For $m \geq 3$ and $k>1 $ holds that $k^{m+1}\geq 1+k^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71332 (m : ℕ) (k : ℕ) : m >= 3 ∧ k > 1 → k^(m+1) ≥ 1 + k^2   :=  by sorry
