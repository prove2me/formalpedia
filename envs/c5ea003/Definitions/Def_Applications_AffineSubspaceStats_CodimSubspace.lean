-- Prove2me | Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
-- name    : Applications_AffineSubspaceStats_CodimSubspace
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:46.316249+00:00
-- url     : https://prove2.me/theorems/bd7a7bdd-74c3-43ac-bffa-b2b2ba5661c6
-- title:
--   Aether Catalog definitions — Applications_AffineSubspaceStats_CodimSubspace
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AffineSubspaceStats.CodimSubspace`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AffineSubspaceStats/CodimSubspace.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
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

namespace AffineStats

open Finset

section Codim

variable {n m d : ℕ}

/-- Projection of `𝔽₂ⁿ` onto its first `m` coordinates. -/
def proj (hmn : m ≤ n) (x : Vec n) : Vec m := fun j => x (Fin.castLE hmn j)

/-- The preimage `π⁻¹(S)` of a set `S ⊆ 𝔽₂^m` under the projection: a union of `|S|`
parallel flats of codimension `m` in `𝔽₂ⁿ`. -/
def unionFlats (hmn : m ≤ n) (S : Finset (Vec m)) : Finset (Vec n) :=
  univ.filter fun x => proj hmn x ∈ S

/-- The codimension-`m` coordinate subspace `{x : x₀ = ⋯ = x_{m-1} = 0}` of `𝔽₂ⁿ`. -/
def codimSub (n : ℕ) (hmn : m ≤ n) : Finset (Vec n) := unionFlats hmn {0}


/-- The linear map `𝔽₂^d → 𝔽₂^m`, `y ↦ ∑ yᵢ wᵢ`, induced by a tuple of vectors. -/
noncomputable def Lmap (w : Fin d → Vec m) : (Fin d → ZMod 2) →ₗ[ZMod 2] Vec m :=
  Fintype.linearCombination (ZMod 2) w


















end Codim

end AffineStats


