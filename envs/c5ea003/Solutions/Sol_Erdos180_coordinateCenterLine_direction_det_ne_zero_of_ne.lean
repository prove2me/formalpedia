-- Prove2me | solution 1 for Erdos180.coordinateCenterLine_direction_det_ne_zero_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:13:17.494154+00:00
-- url     : https://prove2.me/submissions/e543a2c2-6905-4525-9e27-5f9a50912edd

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    {x y x' y' : K}
    (hxy : x ≠ 0 ∨ y ≠ 0)
    (hxy' : x' ≠ 0 ∨ y' ≠ 0)
    (hne : coordinateCenterLine K x y hxy ≠
      coordinateCenterLine K x' y' hxy') :
    x * y' - x' * y ≠ 0 := by
  intro hdet
  have hscale :
      ∃ t : K, t ≠ 0 ∧ x' = t * x ∧ y' = t * y := by
    rcases hxy with hx | hy
    · let t : K := x' / x
      have hfirst : x' = t * x := by
        dsimp [t]
        field_simp [hx]
      have hsecond : y' = t * y := by
        dsimp [t]
        field_simp [hx]
        linear_combination hdet
      have ht : t ≠ 0 := by
        intro htzero
        have hxzero := hfirst
        have hyzero := hsecond
        rw [htzero, zero_mul] at hxzero hyzero
        exact hxy'.elim (fun h => h hxzero)
          (fun h => h hyzero)
      exact ⟨t, ht, hfirst, hsecond⟩
    · let t : K := y' / y
      have hsecond : y' = t * y := by
        dsimp [t]
        field_simp [hy]
      have hfirst : x' = t * x := by
        dsimp [t]
        field_simp [hy]
        linear_combination -hdet
      have ht : t ≠ 0 := by
        intro htzero
        have hxzero := hfirst
        have hyzero := hsecond
        rw [htzero, zero_mul] at hxzero hyzero
        exact hxy'.elim (fun h => h hxzero)
          (fun h => h hyzero)
      exact ⟨t, ht, hfirst, hsecond⟩
  obtain ⟨t, ht, hfirst, hsecond⟩ := hscale
  apply hne
  apply Subtype.ext
  change
    LinearMap.range (coordinateCenterLinearMap K x y) =
      LinearMap.range (coordinateCenterLinearMap K x' y')
  have hmap (u : Fin 2 → K) :
      coordinateCenterLinearMap K x' y' u =
        t • coordinateCenterLinearMap K x y u := by
    funext i
    fin_cases i <;>
      simp [coordinateCenterLinearMap,
        symplecticHorizontalVector,
        symplecticAnnihilatorVector,
        smul_eq_mul, hfirst, hsecond] <;>
      ring
  apply le_antisymm
  · intro w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨t⁻¹ • u, ?_⟩
    rw [hmap, map_smul]
    simp [ht]
  · intro w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨t • u, ?_⟩
    rw [map_smul, ← hmap]
