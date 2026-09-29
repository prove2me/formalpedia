-- Prove2me | Theorems.Thm_lean_workbook_plus_41292
-- name    : lean_workbook_plus_41292
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3c936e4b-2252-4cdb-a599-2717bb096ae9
-- statement:
--   Alternative solution using double angle identity: $\sin \theta = 2 \sin \frac{\theta}{2} \cos \frac{\theta}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41292 :
  ∀ θ : ℝ, θ ≠ 0 → θ ≠ π → sin θ = 2 * sin (θ / 2) * cos (θ / 2)   :=  by sorry
