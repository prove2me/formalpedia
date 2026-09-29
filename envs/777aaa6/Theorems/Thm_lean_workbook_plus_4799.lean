-- Prove2me | Theorems.Thm_lean_workbook_plus_4799
-- name    : lean_workbook_plus_4799
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/be20b203-0f95-4acd-85d8-3301808eb28e
-- statement:
--   Therefore, the answer is $\frac{3}{5}+\frac{1}{5}=\boxed{\frac{4}{5}}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4799  (q e : ℚ)
  (h₀ : q = 3 / 5)
  (h₁ : e = 1 / 5) :
  q + e = 4 / 5   :=  by sorry
