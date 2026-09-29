-- Prove2me | Theorems.Thm_lean_workbook_plus_74305
-- name    : lean_workbook_plus_74305
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/00abe364-da85-4a63-b237-aadd60f970e7
-- statement:
--   $11n = \binom{11}{2} + \binom{11}{3} + \binom{11}{4} +\binom{11}{5} = \frac{2^{11}}{2}-\left(1+11\right)$ . Hence, $11n = 1012 \implies n = \boxed{92}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74305  (n : ℕ)
  (h₀ : 11 * n = 2^11 / 2 - (1 + 11)) :
  n = 92   :=  by sorry
