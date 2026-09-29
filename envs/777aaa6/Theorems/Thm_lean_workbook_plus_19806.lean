-- Prove2me | Theorems.Thm_lean_workbook_plus_19806
-- name    : lean_workbook_plus_19806
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a31ec672-556c-46d1-9e6e-bbf77a6e477b
-- statement:
--   Second, for powers 9, you could say : \n $ y = 0\pmod{19}$ implies $ y^9 = 0\pmod{19}$ \n $ y\neq 0\pmod{19}$ implies $ y^{18} = 1\pmod{19}$ (Fermat) \nBut the only squares equal to 1 $ \pmod{19}$ are 1 and 18 (see above) \nAnd so $ y^9$ can only be $ 0,1, 18$ $ \pmod{19}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19806  (y : ℤ)
  (h₀ : 0 < y)
  (h₁ : y < 19) :
  (y^9) % 19 = 0 ∨ (y^9) % 19 = 1 ∨ (y^9) % 19 = 18   :=  by sorry
