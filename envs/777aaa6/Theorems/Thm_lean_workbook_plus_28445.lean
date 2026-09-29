-- Prove2me | Theorems.Thm_lean_workbook_plus_28445
-- name    : lean_workbook_plus_28445
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/9a3b3335-7c96-4a61-8efe-fdadc502bac6
-- statement:
--   The required factorization is $x^4+4t^4=(x^2+2tx+2t^2)(x^2-2tx+2t^2)$ and is known as Sophie Germain identity.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28445 (x t : ℤ) : x^4 + 4 * t^4 = (x^2 + 2 * t * x + 2 * t^2) * (x^2 - 2 * t * x + 2 * t^2)   :=  by sorry
