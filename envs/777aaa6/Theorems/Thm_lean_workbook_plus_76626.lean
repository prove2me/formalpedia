-- Prove2me | Theorems.Thm_lean_workbook_plus_76626
-- name    : lean_workbook_plus_76626
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b0a7704a-dccc-4ee7-929e-31a649eae81c
-- statement:
--   I found that (1). if $ k\leq -4$ , then $\alpha_k=k+\frac{9}{2}$ . (2). if $-4\leq k\leq 3$ , then $\alpha_k=\frac{k+5}{2}$ . (3). if $k\geq 3$ , then $\alpha_k=2\sqrt{k+1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76626 ∀ k, (k ≤ -4 → α_k = k + 9/2) ∧ (-4 ≤ k ∧ k ≤ 3 → α_k = (k + 5)/2) ∧ (k ≥ 3 → α_k = 2 * Real.sqrt (k + 1))   :=  by sorry
