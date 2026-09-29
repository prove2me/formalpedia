-- Prove2me | Theorems.Thm_lean_workbook_plus_73420
-- name    : lean_workbook_plus_73420
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/4bc8a341-60b2-443d-bd14-c1dc2b890fc5
-- statement:
--   Calculate $\frac{p_1}{q_1} = \frac{5*2 - 7}{14}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73420 (p q : ℤ) (hp : p = 5 * 2 - 7) (hq : q = 14) : p / q = 3 / 14   :=  by sorry
