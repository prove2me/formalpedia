-- Prove2me | Theorems.Thm_mme_dwz_q6_grade_one_coord_leftGrade
-- name    : mme_dwz_q6_grade_one_coord_leftGrade
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:52:51.100298+00:00
-- url     : https://prove2.me/theorems/4425538a-b346-4c3f-976b-12a75b120b2a
-- title:
--   The canonical q=6 grade-one decoder preserves the left fine grade
-- statement:
--   Under the canonical equivalence between the twelve q=6 coarse-grade-one square coordinates and two copies of a six-element set, the left fine grade is 0 on the first copy and 1 on the second. This is the exact histogram translation used by the literal Table-2 allowed-word projector.
-- source:
--   Duan, Wu, and Zhou, arXiv:2210.10173v5, Table 2 and Definition 5.4.

import Definitions.Def_mme_dwz_q6_grade_one_coord_data

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_grade_one_coord_leftGrade
    (p : LiftedCoarsePair.{u} 6 1) :
    p.leftGrade =
      Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
        (fun _ : Fin 6 ↦ (1 : Fin 3)) (dwzQ6GradeOneCoord p) := by
  sorry
