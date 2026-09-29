-- Prove2me | solution 1 for AffineStats.surj_of_cnt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:46:09.769209+00:00
-- url     : https://prove2.me/submissions/700bb239-7af0-4201-ac60-2a8e925defe1

-- Sol generated from Applications/AffineSubspaceStats/CodimSubspace.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Theorems.Thm_AffineStats_card_Vec
import Theorems.Thm_AffineStats_card_image_mul_fiber
import Theorems.Thm_AffineStats_pt_apply
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

















/-- The intersection of the cube with the codimension-`m` subspace is a fiber of the
induced linear map. -/
theorem cnt_codimSub_eq_card_fiber (hmn : m ≤ n) (c : Vec n) (v : Fin d → Vec n) :
    cnt (codimSub n hmn) c v
      = (univ.filter fun y : Fin d → ZMod 2 =>
          (Lmap fun i => proj hmn (v i)) y = proj hmn c).card := by
  have hz : ∀ a b : ZMod 2, (a + b = 0 ↔ b = a) := by decide
  rw [cnt]
  refine congrArg Finset.card (Finset.filter_congr fun y _ => ?_)
  simp only [codimSub, unionFlats, mem_filter, mem_univ, true_and, Lmap,
    Fintype.linearCombination, LinearMap.coe_mk, AddHom.coe_mk, proj, funext_iff,
    Finset.mem_singleton, Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pt_apply]
  exact forall_congr' fun j => hz _ _








open AffineStats in
theorem solution(hmn : m ≤ n) (hmd : m ≤ d) (c : Vec n) (v : Fin d → Vec n)
    (h : cnt (codimSub n hmn) c v = 2 ^ (d - m)) :
    Function.Surjective (Lmap fun i => proj hmn (v i)) := by
  classical
  set L := (Lmap fun i => proj hmn (v i)) with hL
  rw [cnt_codimSub_eq_card_fiber hmn c v, ← hL] at h
  have hne : (univ.filter fun y : Fin d → ZMod 2 => L y = proj hmn c).Nonempty := by
    rw [← Finset.card_pos, h]; positivity
  obtain ⟨y₀, hy₀⟩ := hne
  have hconst : (univ.filter fun y : Fin d → ZMod 2 => L y = proj hmn c).card
      = (univ.filter fun y : Fin d → ZMod 2 => L y = 0).card := by
    refine Finset.card_nbij' (fun y => y - y₀) (fun z => z + y₀) ?_ ?_ ?_ ?_ <;>
      intro a ha <;> simp_all [sub_eq_add_neg]
  have hfib : (univ.filter fun y : Fin d → ZMod 2 => L y = 0).card = 2 ^ (d - m) := by
    rw [← hconst, h]
  have hmul := card_image_mul_fiber (w := fun i => proj hmn (v i))
  rw [← hL, hfib] at hmul
  have hIcard : (univ.image L).card = 2 ^ m := by
    have h2 : (2 : ℕ) ^ m * 2 ^ (d - m) = 2 ^ d := by
      rw [← pow_add]; congr 1; omega
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos (d - m)) (by rw [hmul, ← h2])
  have hfull : univ.image L = univ := by
    apply Finset.eq_univ_of_card
    rw [hIcard, card_Vec]
  intro b
  have hb : b ∈ univ.image L := by rw [hfull]; exact mem_univ b
  obtain ⟨y, -, hy⟩ := Finset.mem_image.1 hb
  exact ⟨y, hy⟩
