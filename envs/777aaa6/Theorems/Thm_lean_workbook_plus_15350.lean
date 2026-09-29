-- Prove2me | Theorems.Thm_lean_workbook_plus_15350
-- name    : lean_workbook_plus_15350
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/8283233e-e20d-4e4a-b420-55ad08245c89
-- statement:
--   $ \frac{n+1}{2n}\leq 1\implies n+1\leq 2n\implies 1\leq n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15350 (n : ℕ) : (n + 1 ≤ 2 * n) → 1 ≤ n   :=  by sorry
