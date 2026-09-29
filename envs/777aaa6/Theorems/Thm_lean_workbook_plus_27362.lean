-- Prove2me | Theorems.Thm_lean_workbook_plus_27362
-- name    : lean_workbook_plus_27362
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/8b916c16-5d46-4aba-896a-572707e42d41
-- statement:
--   Now, by Cauchy-Schwarz, we have ${(am_{a}+bm_{b}+cm_{c})}^{2}\le (a^{2}+b^{2}+c^{2})(m_{a}^{2}+m_{b}^{2}+m_{c}^{2})
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27362  (a b c : ℝ)
  (ma mb mc : ℝ) :
  (a * ma + b * mb + c * mc)^2 ≤ (a^2 + b^2 + c^2) * (ma^2 + mb^2 + mc^2)   :=  by sorry
