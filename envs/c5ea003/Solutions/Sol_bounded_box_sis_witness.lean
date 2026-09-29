-- Prove2me | solution 1 for bounded_box_sis_witness
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:54:27.531796+00:00
-- url     : https://prove2.me/submissions/8b02f905-a865-41a6-a8a7-b08cb2d0c328

-- Sol generated from Cryptography/GeometricCryptanalysis.lean
import Mathlib
import Definitions.Def_Cryptography_GeometricCryptanalysis
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# A geometric pigeonhole for short modular kernel vectors

This file supplies the short-vector existence statement used by
`Cryptography.ParkingFunctionPolytopes.Core`: a counting (pigeonhole) argument
of Minkowski type showing that a box which is larger than the syndrome space of
a modular linear map contains a nonzero short vector in the kernel of that map.

If the integer box `{0, …, 2B}ⁿ` has more points than the syndrome space
`(ℤ/q)ᵐ`, two distinct box points have the same syndrome under `A`, and their
difference is a nonzero vector `z` with `|zᵢ| ≤ 2B` and `A z ≡ 0 (mod q)`.

This is the elementary combinatorial core of the Short Integer Solution (SIS)
problem: hardness assumptions aside, *existence* of a short kernel vector is
pure counting.
-/

open Finset


/-- Pigeonhole: a box with more points than the syndrome space contains two
distinct points with the same syndrome. -/
theorem exists_ne_sisSyndrome_eq {m n q B : ℕ} [NeZero q]
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hsize : q ^ m < (2 * B + 1) ^ n) :
    ∃ x y : Fin n → Fin (2 * B + 1), x ≠ y ∧
      sisSyndrome (q := q) A (fun i => (x i : ℤ)) =
        sisSyndrome (q := q) A (fun i => (y i : ℤ)) :=
  Fintype.exists_ne_map_eq_of_card_lt
    (fun x : Fin n → Fin (2 * B + 1) => sisSyndrome (q := q) A (fun i => (x i : ℤ)))
    (by simpa using hsize)



theorem solution{m n q B : ℕ} (hq : 0 < q)
    (A : Matrix (Fin m) (Fin n) ℤ)
    (hsize : q ^ m < (2 * B + 1) ^ n) :
    ∃ z : Fin n → ℤ,
      z ≠ 0 ∧
      (∀ i, |z i| ≤ 2 * (B : ℤ)) ∧
      (∀ j : Fin m, (∑ i, A j i * z i : ℤ) ≡ 0 [ZMOD q]) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨x, y, hxy, hsyn⟩ := exists_ne_sisSyndrome_eq (q := q) A hsize
  refine ⟨fun i => (x i : ℤ) - (y i : ℤ), ?_, ?_, ?_⟩
  · intro h
    apply hxy
    funext i
    have : ((x i : ℤ)) - ((y i : ℤ)) = 0 := congrFun h i
    have hx : ((x i : ℤ)) = ((y i : ℤ)) := by linarith
    exact Fin.ext (by exact_mod_cast hx)
  · intro i
    have hx : (x i : ℤ) ≤ 2 * B := by
      have := (x i).isLt
      omega
    have hy : (y i : ℤ) ≤ 2 * B := by
      have := (y i).isLt
      omega
    have hx0 : (0 : ℤ) ≤ (x i : ℤ) := by positivity
    have hy0 : (0 : ℤ) ≤ (y i : ℤ) := by positivity
    rw [abs_le]
    constructor <;> linarith
  · intro j
    have h := congrFun hsyn j
    simp only [sisSyndrome] at h
    have hz : ((∑ i, A j i * ((x i : ℤ) - (y i : ℤ)) : ℤ) : ZMod q) = 0 := by
      push_cast
      simp only [mul_sub, Finset.sum_sub_distrib, sub_eq_zero]
      push_cast at h
      exact h
    exact Int.modEq_zero_iff_dvd.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hz)
