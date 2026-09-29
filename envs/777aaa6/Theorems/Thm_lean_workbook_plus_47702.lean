-- Prove2me | Theorems.Thm_lean_workbook_plus_47702
-- name    : lean_workbook_plus_47702
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/476cedd3-6d6c-4107-8847-99a89dc1b851
-- statement:
--   Use Fermat’s little theorem: $3^{10}\equiv1\pmod{11}$ . And $3^{2002}=\left(3^{10}\right)^{20}\cdot3^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47702 : 3 ^ 10 ≡ 1 [ZMOD 11]   :=  by sorry
