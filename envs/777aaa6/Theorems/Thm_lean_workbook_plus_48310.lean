-- Prove2me | Theorems.Thm_lean_workbook_plus_48310
-- name    : lean_workbook_plus_48310
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/00608c8f-bfc1-47e5-a90d-c3de6773b4d8
-- statement:
--   Prove $(x-y) \prod_{k=0}^{k=n-1} (x^{2^k}+y^{2^k})=x^{2^n}-y^{2^n}$ by induction on $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48310 (x y : ℤ) (n : ℕ) : (x - y) * (∏ k in Finset.range n, (x ^ (2 ^ k) + y ^ (2 ^ k))) = x ^ (2 ^ n) - y ^ (2 ^ n)   :=  by sorry
