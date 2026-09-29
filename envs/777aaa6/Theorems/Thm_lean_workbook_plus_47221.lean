-- Prove2me | Theorems.Thm_lean_workbook_plus_47221
-- name    : lean_workbook_plus_47221
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/7a8a7bd3-50dd-4930-8dfc-c403254049a2
-- statement:
--   we have $ \frac{a+b}{c}+\frac{b+c}{a}+\frac{c+a}{b}-6=\frac{a^2b+ab^2+a^2c+ac^2+b^2c+bc^2-6abc}{abc}$ . The nominator is nonnegative because we have $ \frac{a^2b+ab^2+a^2c+ac^2+b^2c+bc^2}{6}\geq\sqrt[6]{(abc)^6}=abc$ by the AM-GM inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47221 :
  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a + b) / c + (b + c) / a + (c + a) / b - 6 ≥ 0   :=  by sorry
