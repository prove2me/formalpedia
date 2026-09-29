-- Prove2me | solution 1 for RecipeHomotopy.InterchangeStructure.vcomp_assoc
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T23:56:13.475908+00:00
-- url     : https://prove2.me/submissions/0cebf402-b359-49fe-a02e-938b65d0caf3

import Mathlib
import Definitions.Def_Bridges_RecipeHomotopyEckmannHilton
open RecipeHomotopy in
theorem solution {α : Type*} (S : InterchangeStructure α) (a b c : α) :
    S.vcomp (S.vcomp a b) c = S.vcomp a (S.vcomp b c) := by
  -- Eckmann–Hilton: with a shared unit, interchange forces the two compositions to agree
  have heq : ∀ x y, S.vcomp x y = S.hcomp x y := by
    intro x y
    calc S.vcomp x y = S.vcomp (S.hcomp x S.unit) (S.hcomp S.unit y) := by
          rw [S.hcomp_unit_right, S.hcomp_unit_left]
      _ = S.hcomp (S.vcomp x S.unit) (S.vcomp S.unit y) := S.interchange _ _ _ _
      _ = S.hcomp x y := by rw [S.vcomp_unit_right, S.vcomp_unit_left]
  -- and then associativity follows from one more interchange
  calc S.vcomp (S.vcomp a b) c = S.vcomp (S.hcomp a b) (S.hcomp S.unit c) := by
        rw [← heq a b, S.hcomp_unit_left]
    _ = S.hcomp (S.vcomp a S.unit) (S.vcomp b c) := S.interchange _ _ _ _
    _ = S.vcomp a (S.vcomp b c) := by
        rw [S.vcomp_unit_right]
        exact (heq a _).symm
