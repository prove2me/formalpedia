-- Prove2me | Theorems.Thm_lean_workbook_plus_11816
-- name    : lean_workbook_plus_11816
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c1f8fd98-26ed-4113-a7f3-42c1cc8df030
-- statement:
--   $ \Longrightarrow 289|((a^2 - 3a - 19) - 17(a - 7))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11816 : ∀ a : ℤ, 289 ∣ (a^2 - 3*a - 19 - 17*(a - 7))   :=  by sorry
