-- Prove2me | solution 1 for Collinear.mem_segment_of_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T17:32:26.806039+00:00
-- url     : https://prove2.me/submissions/d8560099-8f44-4cb7-a79c-0e3409f480c8

import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Module

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Collinear ℝ s) {a p x : E}
    (ha : a ∈ s) (hp : p ∈ s) (hx : x ∈ s) (f : E →ₗ[ℝ] ℝ)
    (hpos : 0 < f (p - a)) (hle : f p ≤ f x) : p ∈ segment ℝ a x := by
  have hne : a ≠ p := by
    intro h
    simp [h] at hpos
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (hs.mem_affineSpan_of_mem_of_ne ha hp hx hne)
  have hrle : 1 ≤ r := by
    rw [← hr, AffineMap.lineMap_apply_module', map_add, map_smul] at hle
    have hsub := f.map_sub p a
    change f p ≤ r * f (p - a) + f a at hle
    nlinarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hrle
  have hinv : r⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr hrpos.le, inv_le_one_of_one_le₀ hrle⟩
  have hmem := lineMap_mem_segment ℝ a x hinv
  rw [← hr, AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ hrpos.ne',
    AffineMap.lineMap_apply_one] at hmem
  simpa only [hr] using hmem
