-- Prove2me | Theorems.Thm_lean_workbook_plus_22142
-- name    : lean_workbook_plus_22142
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/75607912-5981-427a-a101-98e985879454
-- statement:
--   since $cos(a + b) = cosacosb - sinasinb$ we get $cos^2a + cos^2b + (cosacosb - sinasinb)^2 = 1 + 2cosacosb(cosacosb - sinasinb)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22142 : ∀ a b : ℝ, (cos (a + b))^2 = 1 + 2 * cos a * cos b * (cos a * cos b - sin a * sin b)   :=  by sorry
