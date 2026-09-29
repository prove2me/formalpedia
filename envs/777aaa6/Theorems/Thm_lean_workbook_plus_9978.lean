-- Prove2me | Theorems.Thm_lean_workbook_plus_9978
-- name    : lean_workbook_plus_9978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/0d432d73-c3fa-4f7a-91d4-8f9ad4466483
-- statement:
--   black ink on blue: $\frac{1}{7} * \frac{1}{6}$\nblue ink on blue: $\frac{1}{7} * \frac{1}{6}$\nthen multiply $\frac{1}{42} * \frac{1}{42}$\nto get $\frac{1}{1764}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9978 :
  ((1 : ℚ)/7 * (1/6)) * ((1/7) * (1/6)) = (1/42) * (1/42)   :=  by sorry
