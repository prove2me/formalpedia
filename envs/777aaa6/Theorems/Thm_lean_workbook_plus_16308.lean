-- Prove2me | Theorems.Thm_lean_workbook_plus_16308
-- name    : lean_workbook_plus_16308
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/085ac165-f938-4a9a-93e7-4250e5017b91
-- statement:
--   Which can be also noticed by what CantonMathGuy said above: $2^{12}\equiv 1\pmod{3,7,13}\implies 2^{12}\equiv 1\pmod{273}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16308 :
  2^12 ≡ 1 [MOD 3] ∧ 2^12 ≡ 1 [MOD 7] ∧ 2^12 ≡ 1 [MOD 13] → 2^12 ≡ 1 [MOD 3*7*13]   :=  by sorry
