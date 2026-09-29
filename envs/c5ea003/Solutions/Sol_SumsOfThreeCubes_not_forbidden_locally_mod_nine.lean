-- Prove2me | solution 1 for SumsOfThreeCubes.not_forbidden_locally_mod_nine
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:31:05.262196+00:00
-- url     : https://prove2.me/submissions/b278ba80-90f9-4283-acc4-64864e9e5d97

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
theorem solution{k : ℤ} (h : ¬ ForbiddenModNine k) :
    LocallyRepresentable k 9 := by
  have hnonneg := Int.emod_nonneg k (by norm_num : (9 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 9)
  have hkcast : (k : ZMod 9) = (k % 9 : ℤ) := by
    exact (ZMod.intCast_mod k 9).symm
  unfold ForbiddenModNine at h
  unfold LocallyRepresentable
  interval_cases hk : k % 9
  · exact ⟨0, 0, 0, by rw [hkcast]; norm_num⟩
  · exact ⟨1, 0, 0, by rw [hkcast]; norm_num⟩
  · exact ⟨1, 1, 0, by rw [hkcast]; norm_num⟩
  · exact ⟨1, 1, 1, by rw [hkcast]; norm_num⟩
  · exact (h (Or.inl (by omega))).elim
  · exact (h (Or.inr (by omega))).elim
  · exact ⟨-1, -1, -1, by rw [hkcast]; decide⟩
  · exact ⟨-1, -1, 0, by rw [hkcast]; decide⟩
  · exact ⟨-1, 0, 0, by rw [hkcast]; decide⟩
