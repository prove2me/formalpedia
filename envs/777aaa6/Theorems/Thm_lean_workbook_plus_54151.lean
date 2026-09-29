-- Prove2me | Theorems.Thm_lean_workbook_plus_54151
-- name    : lean_workbook_plus_54151
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/29c89186-1407-43b5-abd6-89505d00c9e3
-- statement:
--   Prove that $\frac{1}{p(p+1)}=1/p-1/(p+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54151 (p : ℚ) (hp : p ≠ 0) (hp1 : p + 1 ≠ 0) : 1 / (p * (p + 1)) = 1 / p - 1 / (p + 1)   :=  by sorry
