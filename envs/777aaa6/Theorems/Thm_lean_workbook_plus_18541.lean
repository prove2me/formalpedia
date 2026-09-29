-- Prove2me | Theorems.Thm_lean_workbook_plus_18541
-- name    : lean_workbook_plus_18541
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/4fb1a64b-9f19-4765-b098-2234a2bdeb44
-- statement:
--   $(1+\frac{1}{3})(1+\frac{1}{3^2})\cdots(1+\frac{1}{3^n})< \sqrt{e}$ is also true.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18541 : ∀ n : ℕ, (∏ k in Finset.range n, (1 + 1 / 3^k)) < e^(1/2)   :=  by sorry
