-- Prove2me | Theorems.Thm_lean_workbook_plus_18560
-- name    : lean_workbook_plus_18560
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/47594d62-cacf-451b-a7c9-117cd19b0210
-- statement:
--   Assuming that $p>3$ is a prime, prove that $p^{2}\mid \left ( 1+\frac{1}{2}+\frac{1}{3}+\cdots +\frac{1}{p-1} \right )\left (p-1 \right )!$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18560 : ∀ p : ℕ, p > 3 ∧ p.Prime → p^2 ∣ (1 + 1 / 2 + 1 / 3 + 1 / (p - 1)) * (p - 1)!   :=  by sorry
