-- Prove2me | Theorems.Thm_AffineStats_cnt_unionFlats
-- name    : AffineStats.cnt_unionFlats
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:17:43.928115+00:00
-- url     : https://prove2.me/theorems/c849f8c5-0434-4bbd-b48e-1db05b623b00
-- title:
--   If the directions project onto a spanning tuple, the cube meets the union of parallel
-- statement:
--   If the directions project onto a spanning tuple, the cube meets the union of parallel
--   flats `π⁻¹(S)` in exactly `|S|·2^{d-m}` points.
--
--   ```lean
--   theorem AffineStats.cnt_unionFlats(hmn : m ≤ n) (S : Finset (Vec m)) (c : Vec n) (v : Fin d → Vec n)
--       (hs : Function.Surjective (Lmap fun i => proj hmn (v i))) :
--       cnt (unionFlats hmn S) c v = S.card * 2 ^ (d - m) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AffineSubspaceStats/CodimSubspace.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AffineSubspaceStats/CodimSubspace.lean#L97

-- Thm stub generated from Applications/AffineSubspaceStats/CodimSubspace.lean
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

theorem AffineStats.cnt_unionFlats(hmn : m ≤ n) (S : Finset (Vec m)) (c : Vec n) (v : Fin d → Vec n)
    (hs : Function.Surjective (Lmap fun i => proj hmn (v i))) :
    cnt (unionFlats hmn S) c v = S.card * 2 ^ (d - m) := by sorry
