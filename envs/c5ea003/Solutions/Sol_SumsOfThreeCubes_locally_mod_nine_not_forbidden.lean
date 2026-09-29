-- Prove2me | solution 1 for SumsOfThreeCubes.locally_mod_nine_not_forbidden
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:31:04.747499+00:00
-- url     : https://prove2.me/submissions/38e42835-ba66-40db-bf85-9620b20b3f15

-- Sol generated from NumberTheory/SumsOfThreeCubes.lean
import Mathlib
import Definitions.Def_NumberTheory_SumsOfThreeCubes

/-!
# Sums of Three Cubes: the Exact Modulo-Nine Obstruction

This file proves that reduction modulo nine gives exactly one obstruction:
a residue is a sum of three cubes in `ZMod 9` precisely when it is not `4`
or `5`. It also records global consequences, sign symmetry, a polynomial
family of integral points, and the corresponding affine-cubic-surface view.
-/

open SumsOfThreeCubes



















open SumsOfThreeCubes in
theorem solution{k : ℤ}
    (h : LocallyRepresentable k 9) : ¬ ForbiddenModNine k := by
  intro hbad
  rcases hbad with h4 | h5
  · revert h
    rw [← Int.emod_add_mul_ediv k 9, h4]
    unfold LocallyRepresentable
    simp +decide
    erw [show (9 : ZMod 9) = 0 by rfl]
    simp +decide
  · unfold LocallyRepresentable at h
    obtain ⟨x, y, z, hxyz⟩ := h
    have hkr : ((k : ℤ) : ZMod 9) = ((5 : ℤ) : ZMod 9) := by
      have h1 : ((k : ℤ) : ZMod 9) = ((k % 9 : ℤ) : ZMod 9) := (ZMod.intCast_mod k 9).symm
      rw [h1, h5]
    rw [hkr] at hxyz
    revert x y z hxyz
    decide
