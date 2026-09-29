-- Prove2me | Theorems.Thm_lean_workbook_plus_71808
-- name    : lean_workbook_plus_71808
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/9d2807fe-48e5-4030-8d59-c70c782c71cb
-- statement:
--   This inequality is equivalent to \n $a^4 + 2a^2b^2 + b^4 + a^2c^2 + 2abc^2 +b^2c^2 \ge 2a^3c + 2abc^2 + 2b^3c + 2ab^2c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71808 : ∀ a b c : ℝ, a^4 + 2*a^2*b^2 + b^4 + a^2*c^2 + 2*a*b*c^2 + b^2*c^2 ≥ 2*a^3*c + 2*a*b*c^2 + 2*b^3*c + 2*a*b^2*c   :=  by sorry
