-- Prove2me | Theorems.Thm_lean_workbook_plus_38640
-- name    : lean_workbook_plus_38640
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/65cb6904-3199-4ff1-bcf0-9706e565e074
-- statement:
--   Prove that the number $\left\lfloor\left(5+\sqrt{35}\right)^{2n-1}\right\rfloor$ is divisible by $10^n$ for each $n\in\mathbb N$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38640 (n : ℕ) : 10^n ∣ (5 + Real.sqrt 35)^(2*n-1)   :=  by sorry
