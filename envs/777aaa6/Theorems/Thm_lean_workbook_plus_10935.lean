-- Prove2me | Theorems.Thm_lean_workbook_plus_10935
-- name    : lean_workbook_plus_10935
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a7567ab9-fce1-4e4e-80fb-bedf6abce4b4
-- statement:
--   So the number of successful pairs is $2\\binom{12}{2}+6\\binom{6}{2}=222$ . This is out of $\\binom{60}{2}=1770$ . So the probability is $\\frac{222}{1770}=\\frac{37}{295}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10935 (2 * Nat.choose 12 2 + 6 * Nat.choose 6 2) / Nat.choose 60 2 = 37 / 295   :=  by sorry
