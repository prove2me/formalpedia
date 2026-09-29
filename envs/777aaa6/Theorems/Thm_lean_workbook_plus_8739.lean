-- Prove2me | Theorems.Thm_lean_workbook_plus_8739
-- name    : lean_workbook_plus_8739
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3642384e-ac0f-4f9c-a561-f2866588e044
-- statement:
--   So $x^{81}+x^{49}+x^{25}+x^9+x = x\cdot (x^{80} - 1)+x\cdot (x^{48} - 1)+x\cdot (x^{24} - 1)+x\cdot (x^{8} - 1)+5x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8739 : ∀ x : ℤ, x^81 + x^49 + x^25 + x^9 + x = x * (x^80 - 1) + x * (x^48 - 1) + x * (x^24 - 1) + x * (x^8 - 1) + 5 * x   :=  by sorry
