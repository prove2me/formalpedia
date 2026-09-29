-- Prove2me | Theorems.Thm_lean_workbook_plus_82391
-- name    : lean_workbook_plus_82391
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b30d03a3-f852-45f9-98bc-3a491ccc84fc
-- statement:
--   Let $ R$ be a commutative ring, $ I,J$ are ideals of $ R$ such that $ I+J=R$ . Show that $ IJ=I \cap J$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82391 (R : Type*) [CommRing R] (I J : Ideal R) (h : I + J = ⊤) : I * J = I ⊓ J   :=  by sorry
