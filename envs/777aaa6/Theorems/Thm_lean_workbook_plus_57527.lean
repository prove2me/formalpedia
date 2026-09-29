-- Prove2me | Theorems.Thm_lean_workbook_plus_57527
-- name    : lean_workbook_plus_57527
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/684dab33-80e9-4694-95ca-944574d4c9a4
-- statement:
--   Let the largest of these 25 number to be $x$ , then $x + (x-2) + (x-4) + (x-6) + \cdots + (x-46) + (x-48) =10000$ $25x-(2+4+6+\cdots+46+48)=10000$ $25x-\dfrac{(2+48)24}{2}=10000$ $25x-25*24=10000$ $x-24=400$ $x=\boxed{424}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57527  (x : ℝ)
  (h₀ : ∑ k in Finset.Icc (1:ℕ) 25, (x - 2 * k) = 10000) :
  x = 424   :=  by sorry
