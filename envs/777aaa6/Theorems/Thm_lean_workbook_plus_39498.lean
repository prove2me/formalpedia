-- Prove2me | Theorems.Thm_lean_workbook_plus_39498
-- name    : lean_workbook_plus_39498
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d129c140-a2db-4c09-8f35-d447dff65597
-- statement:
--   And $x^3 \equiv 0,1,6 \pmod{7} \to 19x^3 \equiv 0,5,2 \pmod{7} \to 19x^3-91y^2 \equiv 0,5,2 \pmod{7}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39498 : ∀ x y : ℤ, (x^3 ≡ 0 [ZMOD 7] ∨ x^3 ≡ 1 [ZMOD 7] ∨ x^3 ≡ 6 [ZMOD 7]) → (19*x^3 - 91*y^2 ≡ 0 [ZMOD 7] ∨ 19*x^3 - 91*y^2 ≡ 5 [ZMOD 7] ∨ 19*x^3 - 91*y^2 ≡ 2 [ZMOD 7])   :=  by sorry
