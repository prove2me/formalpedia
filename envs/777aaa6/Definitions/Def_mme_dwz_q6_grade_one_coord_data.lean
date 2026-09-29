-- Prove2me | Definitions.Def_mme_dwz_q6_grade_one_coord_data
-- name    : mme_dwz_q6_grade_one_coord_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-27T09:45:22.727964+00:00
-- url     : https://prove2.me/theorems/38a79a0c-08d9-4317-bd45-616f9cf4ee45
-- title:
--   Canonical decoder for q=6 coarse-grade-one square coordinates
-- statement:
--   The twelve canonical basis pairs of coarse grade one in the q=6 Coppersmith--Winograd square split into two six-element families: an outer coordinate followed by a middle coordinate, and a middle coordinate followed by an outer coordinate. This definition gives the explicit equivalence with $[6]\sqcup[6]$ used by both cyclic Table-2 source routers. Unlike an arbitrary cardinality equivalence, it preserves the literal left fine grade and therefore supports the prescribed-word projector.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and Section 6.3.

import Definitions.Def_mme_dwz_component_word_projection
import Mathlib.Tactic

namespace MME.DWZComponentRestriction

universe u

set_option autoImplicit false

private theorem q6GradeOnePair_left (i : Fin 6) :
    cwSquarePairGrade 6
      ((0 : Fin 8), ⟨i.val + 1, by omega⟩) = 1 := by
  have hi : i.val + 1 ≠ 7 := by omega
  simp [cwSquarePairGrade, cwSquareCoordGrade, hi]

private theorem q6GradeOnePair_right (i : Fin 6) :
    cwSquarePairGrade 6
      (⟨i.val + 1, by omega⟩, (0 : Fin 8)) = 1 := by
  have hi : i.val + 1 ≠ 7 := by omega
  simp [cwSquarePairGrade, cwSquareCoordGrade, hi]

private def q6GradeOnePairEncode :
    Fin 6 ⊕ Fin 6 → CoarsePair 6 1
  | Sum.inl i =>
      ⟨((0 : Fin 8), ⟨i.val + 1, by omega⟩), q6GradeOnePair_left i⟩
  | Sum.inr i =>
      ⟨(⟨i.val + 1, by omega⟩, (0 : Fin 8)), q6GradeOnePair_right i⟩

private def q6GradeOnePairDecode
    (p : CoarsePair 6 1) : Fin 6 ⊕ Fin 6 :=
  if p.1.1.val = 0 then
    Sum.inl (Fin.ofNat 6 (p.1.2.val - 1))
  else
    Sum.inr (Fin.ofNat 6 (p.1.1.val - 1))

private theorem q6GradeOnePairDecode_encode :
    Function.LeftInverse q6GradeOnePairDecode q6GradeOnePairEncode := by
  intro c
  rcases c with i | i <;> fin_cases i <;> rfl

private theorem q6GradeOnePairEncode_decode :
    Function.RightInverse q6GradeOnePairDecode q6GradeOnePairEncode := by
  rintro ⟨⟨a, b⟩, hp⟩
  apply Subtype.ext
  fin_cases a <;> fin_cases b <;>
    simp [q6GradeOnePairDecode, q6GradeOnePairEncode,
      cwSquarePairGrade, cwSquareCoordGrade] at hp ⊢

/-- The canonical decoder of the twelve q=6 square-basis pairs of coarse
grade one into the two six-element middle-coordinate families. -/
noncomputable def dwzQ6GradeOneCoord :
    LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6) :=
  Equiv.ulift.trans
    { toFun := q6GradeOnePairDecode
      invFun := q6GradeOnePairEncode
      left_inv := q6GradeOnePairEncode_decode
      right_inv := q6GradeOnePairDecode_encode }

end MME.DWZComponentRestriction


