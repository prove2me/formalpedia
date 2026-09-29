-- Prove2me | Theorems.Thm_lean_workbook_plus_69909
-- name    : lean_workbook_plus_69909
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0fc8ebe2-1f22-4719-ba82-74c270d9b2a1
-- statement:
--   Prove that for all integers $n \geq 2$ , $\sum_{k=2}^{n} \frac{1}{\sqrt[k]{(2k)!}} \geq \frac{n-1}{2n+2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69909 (n : ℕ) (hn : 2 ≤ n) : ∑ k in (Finset.Icc 2 n), (1 / (2 * k)! ^ (1 / k)) ≥ (n - 1) / (2 * n + 2)   :=  by sorry
