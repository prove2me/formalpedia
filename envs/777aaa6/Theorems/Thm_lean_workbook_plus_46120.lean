-- Prove2me | Theorems.Thm_lean_workbook_plus_46120
-- name    : lean_workbook_plus_46120
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/82ddee69-61bb-4342-af78-ee4d6dc1c4cb
-- statement:
--   Given $ f(x)^{2}=f(x^2) $, prove that $ f(x)\geq 0 $ if $ x\geq 0 $. Also, given $ f(-x)=-f(x) $, prove that $ f(x)\leq 0 $ if $ x\leq 0 $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46120 (f : ℝ → ℝ) (hf1 : ∀ x, f x ^ 2 = f (x ^ 2)) (hf2 : ∀ x, f (- x) = - f x) : ∀ x ≥ 0, f x ≥ 0   :=  by sorry
