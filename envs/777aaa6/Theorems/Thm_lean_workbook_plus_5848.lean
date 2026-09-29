-- Prove2me | Theorems.Thm_lean_workbook_plus_5848
-- name    : lean_workbook_plus_5848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/3a011b3c-1d53-4531-8798-248f1620da41
-- statement:
--   If each person were indistinguishable, order does not matter: $\binom{5+12-1}{12} = \binom{16}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5848 :
  Nat.choose (5 + 12 - 1) 12 = Nat.choose 16 4   :=  by sorry
