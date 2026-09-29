-- Prove2me | Theorems.Thm_lean_workbook_plus_75904
-- name    : lean_workbook_plus_75904
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/9305c70d-97cb-4fe2-bb2c-6577f0bd756e
-- statement:
--   Therefore we need $c+1\equiv 0\pmod{3}\implies \boxed{c\equiv2\pmod{3}}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75904  (c : ℕ)
  (h₀ : (c + 1) % 3 = 0) :
  c % 3 = 2   :=  by sorry
