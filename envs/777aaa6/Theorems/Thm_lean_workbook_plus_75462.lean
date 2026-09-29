-- Prove2me | Theorems.Thm_lean_workbook_plus_75462
-- name    : lean_workbook_plus_75462
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/64ea4ded-44d9-4b39-aa62-278128b158ef
-- statement:
--   Just an example: $(2+2\sqrt{-5})(3-3\sqrt{-5})=36=6^{2}$ , but the two factors on the left are no squares and are coprime (in the sense of $\gcd(a,b)=1$ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75462 (2 + 2*Real.sqrt (-5)) * (3 - 3*Real.sqrt (-5)) = 36   :=  by sorry
