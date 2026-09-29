-- Prove2me | Theorems.Thm_lean_workbook_plus_70360
-- name    : lean_workbook_plus_70360
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/5be02628-657a-4d28-a00a-fbfc8f0926a2
-- statement:
--   $\log_{10}(2^{100})=100 \log_{10} 2 = 30.103 \Longrightarrow 10^{30} \leq 2^{100} \leq 10^{31}.$ Therefore, it has $31$ digits.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70360 :
  (10:ℝ)^30 ≤ 2^100 ∧ 2^100 ≤ (10:ℝ)^31   :=  by sorry
