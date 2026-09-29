-- Prove2me | solution 1 for AffineStats.card_image_mul_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:28:12.791556+00:00
-- url     : https://prove2.me/submissions/386f44f0-6802-4c2b-b5b8-d85cba3cc02c

-- Sol generated from Applications/AffineSubspaceStats/CodimSubspace.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
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
theorem solution(w : Fin d → Vec m) :
    (univ.image (Lmap w)).card * (univ.filter fun y : Fin d → ZMod 2 => Lmap w y = 0).card
      = 2 ^ d := by
  classical
  have hconst : ∀ b' ∈ univ.image (Lmap w),
      (univ.filter fun y : Fin d → ZMod 2 => Lmap w y = b').card
      = (univ.filter fun y : Fin d → ZMod 2 => Lmap w y = 0).card := by
    intro b' hb'
    obtain ⟨y₀, -, hy₀⟩ := Finset.mem_image.1 hb'
    refine Finset.card_nbij' (fun y => y - y₀) (fun z => z + y₀) ?_ ?_ ?_ ?_ <;>
      intro a ha <;> simp_all [sub_eq_add_neg]
  have h := Finset.card_eq_sum_card_fiberwise
      (f := fun y : Fin d → ZMod 2 => Lmap w y) (s := univ)
      (t := univ.image (Lmap w)) (fun x _ => Finset.mem_image_of_mem _ (mem_univ x))
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul] at h
  simp only [Finset.card_univ] at h
  rw [← h]
  simp [ZMod.card]
