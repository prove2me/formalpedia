-- Prove2me | Theorems.Thm_lean_workbook_plus_42896
-- name    : lean_workbook_plus_42896
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/d2169f0b-83e6-4558-b17a-2447c4fbe928
-- statement:
--   Show that if $m = n^2$ where $m$ and $n$ are natural numbers, then $m$ is a perfect square.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42896 (m n : ℕ) (h₁ : m = n^2): ∃ k, k^2 = m   :=  by sorry
