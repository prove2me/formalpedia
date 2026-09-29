-- Prove2me | solution 1 for AffineStats.flatProb_codimSub_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:48:30.444704+00:00
-- url     : https://prove2.me/submissions/908427fc-eac8-4706-9209-04346d99b84f

-- Sol generated from Applications/AffineSubspaceStats/CodimSubspace.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Theorems.Thm_AffineStats_card_Vec
import Theorems.Thm_AffineStats_cnt_unionFlats
import Theorems.Thm_AffineStats_surj_of_cnt
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









/-- If the directions project onto a spanning tuple, the cube meets the codimension-`m`
subspace in exactly `2^{d-m}` points. -/
lemma cnt_codimSub (hmn : m ≤ n) (c : Vec n) (v : Fin d → Vec n)
    (hs : Function.Surjective (Lmap fun i => proj hmn (v i))) :
    cnt (codimSub n hmn) c v = 2 ^ (d - m) := by
  rw [codimSub, cnt_unionFlats hmn _ c v hs, Finset.card_singleton, one_mul]
















open AffineStats in
theorem solution(hmn : m ≤ n) (hmd : m ≤ d) :
    flatProb n d (codimSub n hmn) (2 ^ (d - m))
      = ((univ.filter fun v : Fin d → Vec n =>
          Function.Surjective (Lmap fun i => proj hmn (v i))).card : ℚ) / 2 ^ (n * d) := by
  classical
  have hset : hitSet n d (codimSub n hmn) (2 ^ (d - m))
      = (univ : Finset (Vec n)) ×ˢ (univ.filter fun v : Fin d → Vec n =>
          Function.Surjective (Lmap fun i => proj hmn (v i))) := by
    ext p
    simp only [hitSet, mem_filter, mem_univ, true_and, Finset.mem_product]
    exact ⟨fun h => surj_of_cnt hmn hmd p.1 p.2 h, fun h => cnt_codimSub hmn p.1 p.2 h⟩
  rw [flatProb, hset, Finset.card_product, Finset.card_univ, card_Vec]
  have hden : (2 : ℚ) ^ (n * (d + 1)) = 2 ^ n * 2 ^ (n * d) := by
    rw [← pow_add]; ring_nf
  rw [hden]
  push_cast
  rw [mul_div_mul_left _ _ (by positivity : (2 : ℚ) ^ n ≠ 0)]
