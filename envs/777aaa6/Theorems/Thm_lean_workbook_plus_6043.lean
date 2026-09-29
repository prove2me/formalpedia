-- Prove2me | Theorems.Thm_lean_workbook_plus_6043
-- name    : lean_workbook_plus_6043
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/465dadda-783b-449c-9d4c-2cb4da49fc66
-- statement:
--   Let now $c_n =b_n+2$. Then arrive at $(n+1)c_{n+1}=2(2n+1)c_n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6043 (b : ℕ → ℕ) (hb: b 0 = 1) (hb1: ∀ n:ℕ, b (n + 1) = (2 * n + 1) / (n + 1) * b n) (c : ℕ → ℕ) (hc: c = fun n:ℕ => b n + 2): (n + 1) * c (n + 1) = 2 * (2 * n + 1) * c n   :=  by sorry
