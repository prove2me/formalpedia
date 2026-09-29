-- Prove2me | Theorems.Thm_lean_workbook_plus_60461
-- name    : lean_workbook_plus_60461
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/02425b2b-e8fa-4b25-a864-6f434f3ad34d
-- statement:
--   Prove the equalities\n$ sin^{6}x + cos^{6}x=1-3sin^{2}x*cos^{2}x $\n$ 2(cos^{6}x+sin^{6}x) - 3(sin^{4}x+cos^{4}x) + 1 =0 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60461 : sin x ^ 6 + cos x ^ 6 = 1 - 3 * (sin x ^ 2 * cos x ^ 2)   :=  by sorry
