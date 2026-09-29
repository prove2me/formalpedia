-- Prove2me | Theorems.Thm_mme_complete_split_112_coupled_basis_label_certificate
-- name    : mme_complete_split_112_coupled_basis_label_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:17:22.065649+00:00
-- url     : https://prove2.me/theorems/ccae44a3-de52-4f85-9a4f-3f72cc0eaa1d
-- title:
--   Concrete coupled112 bases carry the exact canonical complete-word labels
-- statement:
--   Let K be any field and q a nonnegative integer. For the specific standard-coordinate grading of the coupled112 tensor, its basis vectors are the existing standard coupled vectors. The two canonical CW grades of each named source pair equal the complete fine word prescribed by that coordinate's actual internal grade. Universe-lifted basis vectors represent those same coordinates and belong to the corresponding concrete grading classes. Thus the canonical source router, complete-word histogram and graded power-basis projections use one verified common coordinate convention; no label compatibility is assumed.
-- source:
--   Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, J.Symbolic Computation9 (1990), coupled constituent pp266,270. Complete-word consumer: Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4-3.6. Exact coordinate order agrees with the accepted general-q canonical112 full-basis router f8c5dc6a-c5b8-4d27-8a41-490338a52d1f.

import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Mathlib.Tactic

set_option autoImplicit false

universe u

open MME MME.CompleteSplit112 Module

theorem mme_complete_split_112_coupled_basis_label_certificate
    (K : Type u) [Field K] (q : ℕ) :
    (∀ (s : Fin 3) (c : DWZCanonical112Coord q s),
      coordBasis K q s c = dwzCanonical112Vec K q s c) ∧
    (∀ (s : Fin 3) (c : DWZCanonical112Coord q s),
      ![cwSquareCoordGrade q (dwzCanonical112Pair q s c).1,
        cwSquareCoordGrade q (dwzCanonical112Pair q s c).2] =
        fineWord s (coordGrade q s c)) ∧
    (∀ (s : Fin 3) (c : LiftedCoord.{u} q s),
      liftedCoordBasis K q s c = dwzCanonical112Vec K q s c.down) ∧
    (∀ (s : Fin 3) (c : LiftedCoord.{u} q s),
      liftedCoordBasis K q s c ∈
        (grading K q).classOf s (liftedCoordGrade q s c)) := by sorry
