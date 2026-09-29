-- Prove2me | Theorems.Thm_lean_workbook_plus_64182
-- name    : lean_workbook_plus_64182
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d41d1dfa-110d-4645-b1e9-c8bc37df43bc
-- statement:
--   Continue with nguoivn's approach in detailed: By Holder, we have: $(LHS)^2(\sum a(a+b))\ge (a+b+c)^3$ $\Longleftrightarrow (LHS)^2\ge \frac {(a+b+c)^3}{\sum a(a+b)}$ Hence so as to prove the inequality of the problem, it is enough to prove: $ 2(a+b+c)^3\ge 9(a^2+b^2+c^2+ab+bc+ca)$ , $ (*)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64182 :
  ∀ a b c : ℝ,
    2 * (a + b + c) ^ 3 ≥ 9 * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a)   :=  by sorry
