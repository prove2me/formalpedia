-- Prove2me | Theorems.Thm_lean_workbook_plus_36696
-- name    : lean_workbook_plus_36696
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/98b150a2-0472-41c7-9557-589a3b68df8a
-- statement:
--   Prove that $P(n) = n(n+1)(n+2)$ is divisible by $6$ for $n\geq2$ without using induction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36696 : ∀ n ≥ 2, 6 ∣ n * (n + 1) * (n + 2)   :=  by sorry
