-- Prove2me | Theorems.Thm_lean_workbook_plus_8957
-- name    : lean_workbook_plus_8957
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/8aaffb66-ff13-4834-9e1a-92ebccb76664
-- statement:
--   Given $k=a+b+c$, let $a_{1}=\frac{a}{k}$, $b_{1}=\frac{b}{k}$, $c_{1}=\frac{c}{k}$. Show that $a_{1}+b_{1}+c_{1}=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8957 (a b c k : ℝ) (h₁ : k = a + b + c) (h₂ : a + b + c ≠ 0) : a / k + b / k + c / k = 1   :=  by sorry
