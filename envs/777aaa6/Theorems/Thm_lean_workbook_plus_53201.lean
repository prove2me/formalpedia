-- Prove2me | Theorems.Thm_lean_workbook_plus_53201
-- name    : lean_workbook_plus_53201
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/64cbab22-e238-40b6-9678-4a86191a0240
-- statement:
--   Show that $\frac{1}{n+1}\left(1+\frac{1}{3}+\cdots+\frac{1}{2n-1}\right)>\frac{1}{n}\left(\frac{1}{2}+\frac{1}{4}+\cdots+\frac{1}{2n}\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53201 : ∀ n : ℕ, (1 / (n + 1)) * ∑ i in Finset.range n, (1 / (2 * i + 2)) < (1 / n) * ∑ i in Finset.range n, (1 / (2 * i + 1))   :=  by sorry
