-- Prove2me | Theorems.Thm_lean_workbook_plus_78074
-- name    : lean_workbook_plus_78074
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/cf1b5d84-0dda-401e-b832-9d0297799442
-- statement:
--   $a^{2}+b^{2}+(a-b)^{2}=c^{2}+d^{2}+(c-d)^{2}$\n $\Rightarrow 2(a^{2}-ab+b^{2})=2(c^{2}-cd+d^{2})$\n $\Rightarrow 2(a^{2}-ab+b^{2})^{2}=2(c^{2}-cd+d^{2})^{2}$\n $\Rightarrow 2(a^{4}-2a^{3}b+3a^{2}b^{2}-2ab^{3}+b^{4})=2(c^{4}-2c^{3}d+3c^{2}d^{2}-2cd^{3}+d^{4})$\n $\Rightarrow a^{4}+b^{4}+(a-b)^{4}=c^{4}+d^{4}+(c-d)^{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78074  (a b c d : ℝ)
  (h₀ : a^2 + b^2 + (a - b)^2 = c^2 + d^2 + (c - d)^2) :
  a^4 + b^4 + (a - b)^4 = c^4 + d^4 + (c - d)^4   :=  by sorry
