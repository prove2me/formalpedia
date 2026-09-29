-- Prove2me | Theorems.Thm_lean_workbook_plus_37984
-- name    : lean_workbook_plus_37984
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/09aaa4b6-3534-4c74-bdc7-60e887690581
-- statement:
--   $(x+y+z)^{3}=x^{3}+y^{3}+z^{3}+3xy(x+y)+3yz(y+z)+3zx(z+x)+6xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37984 : (x + y + z) ^ 3 = x ^ 3 + y ^ 3 + z ^ 3 + 3 * x * y * (x + y) + 3 * y * z * (y + z) + 3 * z * x * (z + x) + 6 * x * y * z   :=  by sorry
