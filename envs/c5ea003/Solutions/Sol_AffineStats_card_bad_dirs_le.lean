-- Prove2me | solution 1 for AffineStats.card_bad_dirs_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:25:08.766192+00:00
-- url     : https://prove2.me/submissions/032ca4d9-9a39-4ae6-8a6b-246033e295e7

-- Sol generated from Applications/AffineSubspaceStats/CodimSubspace.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Theorems.Thm_AffineStats_card_Vec
import Theorems.Thm_AffineStats_card_orth_dirs
import Theorems.Thm_AffineStats_exists_orth_of_not_surjective
/-
# Affine subspace statistics in `𝔽₂ⁿ`: the codimension-`m` lower bound construction

This file continues the development of
`Catalog/Applications/AffineSubspaceStats/AffineStats.lean`, where the model
(random affine `d`-cubes in `𝔽₂ⁿ`, the statistic `cnt`, the probability `flatProb`)
is set up, and where the codimension-one case was computed exactly
(`AffineStats.hyperplane_flatProb`).

Here we treat arbitrary codimension `m`.  Let `A ⊆ 𝔽₂ⁿ` be the codimension-`m`
subspace `{x : x₀ = ⋯ = x_{m-1} = 0}` and let `F` be a uniformly random affine
`d`-cube.  Writing `π` for the projection onto the first `m` coordinates, the cube
`y ↦ c + ∑ yᵢvᵢ` meets `A` in exactly `2^{d-m}` points as soon as the linear map
`y ↦ ∑ yᵢ π(vᵢ)` is surjective, and surjectivity fails with probability at most
`(2^m - 1)/2^d` by a union bound over the nonzero linear functionals annihilating
the image.  Consequently, with `k = d - m`,

`P[|F ∩ A| = 2^k] ≥ 1 - 2^{-k} + 2^{-d}`,

which is the standard lower-bound construction `λ*(d, 2^k) ≥ 1 - 2^{-k}` for the
affine subspace statistics problem (with an explicit improvement `2^{-d}`).

The same argument applies verbatim to a union of `j` parallel flats of codimension `m`,
i.e. to `A = π⁻¹(S)` with `|S| = j`: the cube then meets `A` in exactly `j·2^{d-m}` points,
which gives the paper's lower-bound construction `λ*(d, j·2^k) ≥ 1 - 2^{-k}`
(`AffineStats.exists_flatProb_mul_pow_two_ge`).
-/

open AffineStats

open Finset


variable {n m d : ℕ}

























open AffineStats in
theorem solution(hmn : m ≤ n) :
    2 ^ d * (univ.filter fun v : Fin d → Vec n =>
        ¬ Function.Surjective (Lmap fun i => proj hmn (v i))).card
      ≤ (2 ^ m - 1) * 2 ^ (n * d) := by
  have hsub : (univ.filter fun v : Fin d → Vec n =>
      ¬ Function.Surjective (Lmap fun i => proj hmn (v i)))
      ⊆ (univ.filter fun a : Vec m => a ≠ 0).biUnion
          (fun a => univ.filter fun v : Fin d → Vec n =>
            ∀ i, ∑ j, a j * proj hmn (v i) j = 0) := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and] at hv
    obtain ⟨a, ha0, ha⟩ := exists_orth_of_not_surjective _ hv
    exact mem_biUnion.2 ⟨a, by simp [ha0], by simpa using ha⟩
  have hcard := Finset.card_le_card hsub
  have hbu := Finset.card_biUnion_le (s := univ.filter fun a : Vec m => a ≠ 0)
    (t := fun a => univ.filter fun v : Fin d → Vec n =>
      ∀ i, ∑ j, a j * proj hmn (v i) j = 0)
  have hnz : (univ.filter fun a : Vec m => a ≠ 0).card = 2 ^ m - 1 := by
    have hers : (univ.filter fun a : Vec m => a ≠ 0) = univ.erase (0 : Vec m) := by
      ext a; simp [Finset.mem_erase]
    rw [hers, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, card_Vec]
  calc 2 ^ d * (univ.filter fun v : Fin d → Vec n =>
      ¬ Function.Surjective (Lmap fun i => proj hmn (v i))).card
      ≤ 2 ^ d * ∑ a ∈ univ.filter fun a : Vec m => a ≠ 0,
          (univ.filter fun v : Fin d → Vec n =>
            ∀ i, ∑ j, a j * proj hmn (v i) j = 0).card :=
        Nat.mul_le_mul_left _ (le_trans hcard hbu)
    _ = ∑ a ∈ univ.filter fun a : Vec m => a ≠ 0, 2 ^ d *
          (univ.filter fun v : Fin d → Vec n =>
            ∀ i, ∑ j, a j * proj hmn (v i) j = 0).card := by rw [Finset.mul_sum]
    _ = ∑ _a ∈ univ.filter fun a : Vec m => a ≠ 0, 2 ^ (n * d) :=
        Finset.sum_congr rfl fun a ha =>
          card_orth_dirs hmn a (by simpa using (mem_filter.1 ha).2)
    _ = (2 ^ m - 1) * 2 ^ (n * d) := by rw [Finset.sum_const, hnz, smul_eq_mul]
