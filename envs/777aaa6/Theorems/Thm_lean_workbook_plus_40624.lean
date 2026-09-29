-- Prove2me | Theorems.Thm_lean_workbook_plus_40624
-- name    : lean_workbook_plus_40624
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/24b10ace-6378-454f-96ea-fe57afa00020
-- statement:
--   $AB^2 - ABA = 0 \iff AB^2 = ABA$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40624 (R : Type*) [CommRing R]
  (A B : Matrix (Fin 2) (Fin 2) R) :
  A * B ^ 2 - A * B * A = 0 ↔ A * B ^ 2 = A * B * A   :=  by sorry
