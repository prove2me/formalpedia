-- Prove2me | Theorems.Thm_lean_workbook_plus_52027
-- name    : lean_workbook_plus_52027
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/866b4ea0-147c-4140-9973-7f8a082f0235
-- statement:
--   Your inequality is linear of $abc$ . Hence, by $uvw$ we need to check two cases: 1. $abc\rightarrow0^+$ . In this case our inequality is obviously true; 2. $b=c=1$ , which gives $(a+2)^8\geq243(2a^2+1)(2a+1)^2$ . The last inequality we can prove by calculus.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52027  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a * b * c = 1) :
  (a + 2)^8 ≥ 243 * (2 * a^2 + 1) * (2 * a + 1)^2   :=  by sorry
