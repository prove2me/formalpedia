-- Prove2me | Theorems.Thm_lean_workbook_plus_56716
-- name    : lean_workbook_plus_56716
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/427f6a4e-9d8a-41a1-b776-02892a6450b7
-- statement:
--   Let $a+b+c=1$ . By Cauchy, the inequality reduces to $\frac{2}{3(a^{2}+b^{2}+c^{2})+5(ab+bc+ca)}\geq{\frac{1}{4(a^{2}+b^{2}+c^{2})}}$ which is equivalent to $a^{2}+b^{2}+c^{2}\geq{ab+bc+ca}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56716  (a b c: ℝ)
  (h₀ : a + b + c = 1) :
  a^2 + b^2 + c^2 ≥ a * b + b * c + c * a   :=  by sorry
