-- Prove2me | solution 1 for LeblRA.two_point_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:13:49.183743+00:00
-- url     : https://prove2.me/submissions/431a3bd5-0d0b-4c7e-b001-6b10cefba54a

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open Set Filter Topology
open scoped ContinuousMapZero
open scoped Polynomial

namespace LeblRA

private theorem interpolate {K X B : Type*} [Field K] [CommRing B] [Algebra K B]
    (A : NonUnitalSubalgebra K B) (E : B →ₐ[K] (X → K))
    (sep : ∀ x y : X, x ≠ y → ∃ g ∈ A, E g x ≠ E g y)
    (nv : ∀ x : X, ∃ g ∈ A, E g x ≠ 0)
    (x y : X) (hxy : x ≠ y) (c d : K) :
    ∃ f ∈ A, E f x = c ∧ E f y = d := by
  obtain ⟨g, hg, hsep⟩ := sep x y hxy
  obtain ⟨h, hh, hx⟩ := nv x
  obtain ⟨k, hk, hy⟩ := nv y
  let u := g * h - (E g y) • h
  let v := g * k - (E g x) • k
  have hu : u ∈ A := A.sub_mem (A.mul_mem hg hh) (A.smul_mem _ hh)
  have hv : v ∈ A := A.sub_mem (A.mul_mem hg hk) (A.smul_mem _ hk)
  refine ⟨(c / ((E g x - E g y) * E h x)) • u +
    (d / ((E g y - E g x) * E k y)) • v,
    A.add_mem (A.smul_mem _ hu) (A.smul_mem _ hv), ?_, ?_⟩
  · simp only [map_add, map_smul, map_sub, map_mul, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, Pi.mul_apply, smul_eq_mul, u, v]
    field_simp [sub_ne_zero.mpr hsep, sub_ne_zero.mpr hsep.symm, hx, hy]
    ring
  · simp only [map_add, map_smul, map_sub, map_mul, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, Pi.mul_apply, smul_eq_mul, u, v]
    field_simp [sub_ne_zero.mpr hsep, sub_ne_zero.mpr hsep.symm, hx, hy]
    ring

theorem _root_.solution (X : Type*) :
    (∀ A : NonUnitalSubalgebra ℝ (X → ℝ),
      (∀ x y : X, x ≠ y → ∃ g ∈ A, g x ≠ g y) →
      (∀ x : X, ∃ g ∈ A, g x ≠ 0) →
      ∀ x y : X, x ≠ y → ∀ c d : ℝ, ∃ f ∈ A, f x = c ∧ f y = d) ∧
    (∀ A : NonUnitalSubalgebra ℂ (X → ℂ),
      (∀ x y : X, x ≠ y → ∃ g ∈ A, g x ≠ g y) →
      (∀ x : X, ∃ g ∈ A, g x ≠ 0) →
      ∀ x y : X, x ≠ y → ∀ c d : ℂ, ∃ f ∈ A, f x = c ∧ f y = d) := by
  constructor
  · intro A sep nv x y hxy c d
    exact interpolate A (AlgHom.id ℝ (X → ℝ)) sep nv x y hxy c d
  · intro A sep nv x y hxy c d
    exact interpolate A (AlgHom.id ℂ (X → ℂ)) sep nv x y hxy c d

end LeblRA
