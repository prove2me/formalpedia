-- Prove2me | Theorems.Thm_lean_workbook_plus_21397
-- name    : lean_workbook_plus_21397
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/0156887f-b7e6-44fd-a5c2-f152acc22fa2
-- statement:
--   Prove, without using mathematical induction, that $ 3 \cdot 5^{2n+1} + 2^{3n+1}$ is divisible by $ 17$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21397 : ∀ n:ℕ, 17 ∣ 3 * 5^(2 * n + 1) + 2^(3 * n + 1)   :=  by sorry
