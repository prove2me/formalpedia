-- Prove2me | Theorems.Thm_lean_workbook_plus_48040
-- name    : lean_workbook_plus_48040
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/7f8c26e3-3ec0-42a4-8ea4-dedbf1f32b42
-- statement:
--   Observe that $\frac{2^{56}}{5^{24}} = 1.024^8 = 1.048576^4 < 1.05^4 = 1.1025^2 < 1.11^2 = 1.2321 < 1.25 = \frac{5}{2^2}$ , so $5^{25} > 2^{58}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48040 :
  (5:ℝ)^25 > 2^58   :=  by sorry
