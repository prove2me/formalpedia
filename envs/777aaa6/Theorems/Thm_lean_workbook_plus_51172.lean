-- Prove2me | Theorems.Thm_lean_workbook_plus_51172
-- name    : lean_workbook_plus_51172
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/837e4897-4e75-44fe-8df1-8558748fd4c8
-- statement:
--   Given that $4444^{4444} \equiv 7 \pmod 9$, find the last digit sum of $4444^{4444}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51172 : 4444^4444 ≡ 7 [MOD 9] ∧ (Nat.digits 10 ((4444^4444) % 10)).sum = 7   :=  by sorry
