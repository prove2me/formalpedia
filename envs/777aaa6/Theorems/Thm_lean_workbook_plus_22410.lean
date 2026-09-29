-- Prove2me | Theorems.Thm_lean_workbook_plus_22410
-- name    : lean_workbook_plus_22410
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f1977cfe-3baa-4b1a-b98e-8c0c88c35b18
-- statement:
--   Suppose $ n = k^{2}$ . Then $ \;\sqrt{n}\; = k$ and $ k \;| \;k^{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22410  (n k : ℕ)
  (h₀ : n = k^2) :
  Real.sqrt n = k ∧ k ∣ k^2   :=  by sorry
