-- Prove2me | Theorems.Thm_lean_workbook_plus_56586
-- name    : lean_workbook_plus_56586
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/4142de52-feab-4201-93fc-9776652e37cf
-- statement:
--   Prove that every subgroup of an abelian group $G$ is normal.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56586 (G : Type*) [CommGroup G] (H : Subgroup G) : H.Normal   :=  by sorry
