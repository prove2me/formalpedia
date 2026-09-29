-- Prove2me | Theorems.Thm_lean_workbook_plus_14189
-- name    : lean_workbook_plus_14189
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/12add2fd-8fa1-46dc-93e4-7a9bef606fd4
-- statement:
--   Given that $ k|2a$ and $ k|2b$ , and $ gcd(a,b)=1$ , prove that $ k=1$ or $ 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14189 (k a b : ℕ) (h1 : k ∣ 2 * a) (h2 : k ∣ 2 * b) (h3 : Nat.gcd a b = 1) : k = 1 ∨ k = 2   :=  by sorry
