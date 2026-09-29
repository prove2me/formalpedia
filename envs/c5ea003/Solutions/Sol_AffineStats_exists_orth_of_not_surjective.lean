-- Prove2me | solution 1 for AffineStats.exists_orth_of_not_surjective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:23:25.520714+00:00
-- url     : https://prove2.me/submissions/0e01dbab-c311-4bb7-9cdd-7b5477f35052

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
theorem solution(w : Fin d → Vec m)
    (h : ¬ Function.Surjective (Lmap w)) :
    ∃ a : Vec m, a ≠ 0 ∧ ∀ i, ∑ j, a j * w i j = 0 := by
  have hlt : LinearMap.range (Lmap w) < ⊤ :=
    lt_of_le_of_ne le_top fun hc => h (LinearMap.range_eq_top.1 hc)
  obtain ⟨f, hf0, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  set e : Fin m → Vec m := fun j k => if j = k then (1 : ZMod 2) else 0 with he
  refine ⟨fun j => f (e j), ?_, ?_⟩
  · intro hcon
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    have hz : ∀ j : Fin m, f (e j) = 0 := fun j => congrFun hcon j
    simp [he] at hz ⊢
    simp [hz]
  · intro i
    have hmem : w i ∈ LinearMap.range (Lmap w) :=
      ⟨fun k => if i = k then (1 : ZMod 2) else 0, by
        simp [Lmap, Fintype.linearCombination, ite_smul]⟩
    have hzero : f (w i) = 0 := by
      have hm : f (w i) ∈ Submodule.map f (LinearMap.range (Lmap w)) := ⟨w i, hmem, rfl⟩
      rw [hfmap] at hm
      simpa using hm
    rw [LinearMap.pi_apply_eq_sum_univ f (w i)] at hzero
    rw [← hzero]
    exact Finset.sum_congr rfl fun j _ => by simp [he, mul_comm]
