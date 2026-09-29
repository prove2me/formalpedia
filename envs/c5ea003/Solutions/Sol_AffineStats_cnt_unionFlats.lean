-- Prove2me | solution 1 for AffineStats.cnt_unionFlats
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:40:43.526086+00:00
-- url     : https://prove2.me/submissions/dae1da75-38a0-4704-9607-003258121ae4

-- Sol generated from Applications/AffineSubspaceStats/CodimSubspace.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Theorems.Thm_AffineStats_card_fiber_Lmap
import Theorems.Thm_AffineStats_pt_apply
import Theorems.Thm_AffineStats_vadd_self
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
theorem solution(hmn : m ≤ n) (S : Finset (Vec m)) (c : Vec n) (v : Fin d → Vec n)
    (hs : Function.Surjective (Lmap fun i => proj hmn (v i))) :
    cnt (unionFlats hmn S) c v = S.card * 2 ^ (d - m) := by
  classical
  set L := (Lmap fun i => proj hmn (v i)) with hL
  have hinv : ∀ x y : Vec m, x + y + x = y := by
    intro x y; rw [add_comm x y, add_assoc, vadd_self, add_zero]
  have hpe : ∀ y, proj hmn (pt c v y) = proj hmn c + L y := by
    intro y
    funext j
    simp only [proj, pt_apply, hL, Lmap, Fintype.linearCombination, LinearMap.coe_mk,
      AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  set T := S.image (fun s => s + proj hmn c) with hT
  have hmemT : ∀ z : Vec m, (proj hmn c + z ∈ S) ↔ z ∈ T := by
    intro z
    simp only [hT, Finset.mem_image]
    constructor
    · intro h
      exact ⟨proj hmn c + z, h, hinv _ _⟩
    · rintro ⟨s, hsS, rfl⟩
      have hcs : proj hmn c + (s + proj hmn c) = s := by
        rw [add_comm s (proj hmn c), ← add_assoc, vadd_self, zero_add]
      rwa [hcs]
  have hfilter : (univ.filter fun y : Fin d → ZMod 2 => pt c v y ∈ unionFlats hmn S)
      = univ.filter fun y : Fin d → ZMod 2 => L y ∈ T := by
    refine Finset.filter_congr fun y _ => ?_
    simp only [unionFlats, mem_filter, mem_univ, true_and, hpe y]
    exact hmemT (L y)
  have hcardT : T.card = S.card := by
    rw [hT, Finset.card_image_of_injective _ (fun a b hab => by
      have h2 := congrArg (fun z => z + proj hmn c) hab
      simpa [add_assoc, vadd_self] using h2)]
  rw [cnt, hfilter]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun y : Fin d → ZMod 2 => L y)
    (s := univ.filter fun y : Fin d → ZMod 2 => L y ∈ T) (t := T)
    (fun x hx => (mem_filter.1 hx).2)]
  have hall : ∀ b ∈ T, ((univ.filter fun y : Fin d → ZMod 2 => L y ∈ T).filter
      fun y => L y = b).card = 2 ^ (d - m) := by
    intro b hb
    rw [show ((univ.filter fun y : Fin d → ZMod 2 => L y ∈ T).filter fun y => L y = b)
        = univ.filter (fun y : Fin d → ZMod 2 => L y = b) from by
      ext y
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h; exact ⟨by rw [h]; exact hb, h⟩]
    exact card_fiber_Lmap _ hs b
  rw [Finset.sum_congr rfl hall, Finset.sum_const, hcardT, smul_eq_mul]
