-- Prove2me | Theorems.Thm_lean_workbook_plus_1441
-- name    : lean_workbook_plus_1441
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/b15ab6cd-aed2-42f4-8cb3-225bcaccb1c8
-- statement:
--   Let $ K = {\lfloor a - \frac {1}{2}\rfloor + \lfloor a + \frac {1}{2}\rfloor}$ , where $ a\in \mathbb{R}$\nProve that $ K = 0 (mod 2)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1441 : ∀ a : ℝ, (↑⌊a - 1 / 2⌋ + ↑⌊a + 1 / 2⌋) % 2 = 0   :=  by sorry
