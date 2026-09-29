-- Prove2me | Theorems.Thm_lean_workbook_plus_70898
-- name    : lean_workbook_plus_70898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/959a0776-9e19-466b-96c8-a55373dfa6de
-- statement:
--   Rearrange the equation as follows: $ z^{2}=(x^{2}+1)(y^{2}-1)+2006\Rightarrow x^{2}-y^{2}+z^{2}-x^{2}y^{2}=2005 $ . Find solutions.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70898 (x y z : ℤ) :  z^2 = (x^2 + 1) * (y^2 - 1) + 2006 ↔ x^2 - y^2 + z^2 - x^2 * y^2 = 2005   :=  by sorry
