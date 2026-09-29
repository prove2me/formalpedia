-- Prove2me | Theorems.Thm_lean_workbook_plus_59983
-- name    : lean_workbook_plus_59983
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/8206aad2-b34b-425e-810f-6447d25da4ce
-- statement:
--   It is not needed. The goo gets longer by a factor of $1.6 \times 1.25=2$ every day, so it is just asking the smallest power of 2 that is larger than 2017. The power of 2 is $2^{11}=2048$ , so that will happen at 11 days after the beginniing Monday, which is a Thursday.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59983  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : 2^n > 2017) :
  11 ≤ n   :=  by sorry
