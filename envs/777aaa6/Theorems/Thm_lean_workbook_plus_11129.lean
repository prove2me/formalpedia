-- Prove2me | Theorems.Thm_lean_workbook_plus_11129
-- name    : lean_workbook_plus_11129
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/7d56a112-ee26-4a54-a18d-a9b7cdb55bd4
-- statement:
--   Alternatively, we can use combinatorics. Suppose there are $ x$ number of $ 2$ s. Obviously $ x \ge 5$ . The $ 11-x$ number of $ 1$ s must be inserted in the $ x+1$ slots amongst the $ 2$ s, such that only one $ 1$ can go to any given slot. By the ball-and-urn argument, there are $ {x+1 \choose 11-x}$ ways to do this. Thus the answer is $ \sum^{11}_{n=6} {n+1 \choose 11-n} = 1 + 21 + 70 + 84 + 45 + 11 + 1 = 233$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11129  (x : ℕ)
  (h₀ : 5 ≤ x)
  (h₁ : x ≤ 11) :
  ∑ k in Finset.Icc 5 11, choose (k + 1) (11 - k) = 233   :=  by sorry
