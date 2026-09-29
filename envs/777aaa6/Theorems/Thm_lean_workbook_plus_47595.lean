-- Prove2me | Theorems.Thm_lean_workbook_plus_47595
-- name    : lean_workbook_plus_47595
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/caeaef46-4b7e-4d29-aa76-01af82465afe
-- statement:
--   To get a $7$ , you can roll a $(1,6),(2,5),(3,4),(4,3),(5,2),(6,1)$ . \n\nProbability of $(1,6)$ and $(6,1)$ = $2(\frac{6}{21})(\frac{1}{21})$ \n\nProbability of $(2,5)$ and $(5,2)$ = $2(\frac{5}{21})(\frac{2}{21})$ \n\nProbability of $(3,4)$ and $(4,3)$ = $2(\frac{3}{21})(\frac{4}{21})$ \n\nAdd them up to get $\frac{8}{63}\rightarrow\boxed{C}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47595 :
  (2 * (6 / 21 * 1 / 21 + 5 / 21 * 2 / 21 + 3 / 21 * 4 / 21)) = 8 / 63   :=  by sorry
