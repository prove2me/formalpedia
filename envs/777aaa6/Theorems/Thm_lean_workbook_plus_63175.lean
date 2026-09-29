-- Prove2me | Theorems.Thm_lean_workbook_plus_63175
-- name    : lean_workbook_plus_63175
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/cbe5d4ce-035d-4373-bf91-ed2ee85b76cc
-- statement:
--   Prove that $2(\sqrt{x(y^{29}+z^{2007})}+\sqrt{y^{29}(x+z^{2007})}+\sqrt{z^{2007}(x+y^{29})})\leq3(x+y^{29}+z^{2007})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63175 : ∀ x y z : ℝ, 2 * (Real.sqrt (x * (y^29 + z^2007)) + Real.sqrt (y^29 * (x + z^2007)) + Real.sqrt (z^2007 * (x + y^29))) ≤ 3 * (x + y^29 + z^2007)   :=  by sorry
