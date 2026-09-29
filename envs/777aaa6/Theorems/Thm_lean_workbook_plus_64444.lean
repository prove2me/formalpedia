-- Prove2me | Theorems.Thm_lean_workbook_plus_64444
-- name    : lean_workbook_plus_64444
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6bf0700d-abb7-46aa-b8a3-5b24d6aa40f1
-- statement:
--   Prove the identity $a^5 + b^5 = (a+b)(a^4 - a^3b + a^2b^2 - ab^3 + b^4)$ and extend it to the general form $a^{2n+1} + b^{2n+1} = (a+b)(a^{2n} - a^{2n-1}b + a^{2n-2}b^2 - ... - ab^{2n-1} + b^{2n})$, where $n$ is an integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64444 : ∀ a b : ℤ, a^5 + b^5 = (a + b) * (a^4 - a^3 * b + a^2 * b^2 - a * b^3 + b^4)   :=  by sorry
