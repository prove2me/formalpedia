-- Prove2me | solution 1 for AffineStats.card_fiber_Lmap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:28:12.27012+00:00
-- url     : https://prove2.me/submissions/af47f9cd-c45e-4013-ad80-970d71845c7d

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
theorem solution(w : Fin d → Vec m) (hs : Function.Surjective (Lmap w)) (b : Vec m) :
    (univ.filter fun y : Fin d → ZMod 2 => Lmap w y = b).card = 2 ^ (d - m) := by
  -- all fibers are translates of the kernel, hence have the same size
  have hconst : ∀ b' : Vec m, (univ.filter fun y : Fin d → ZMod 2 => Lmap w y = b').card
      = (univ.filter fun y : Fin d → ZMod 2 => Lmap w y = 0).card := by
    intro b'
    obtain ⟨y₀, hy₀⟩ := hs b'
    refine Finset.card_nbij' (fun y => y - y₀) (fun z => z + y₀) ?_ ?_ ?_ ?_ <;>
      intro a ha <;> simp_all [sub_eq_add_neg]
  set c := (univ.filter fun y : Fin d → ZMod 2 => Lmap w y = 0).card with hc
  have htot : 2 ^ d = 2 ^ m * c := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := fun y : Fin d → ZMod 2 => Lmap w y) (s := univ) (t := (univ : Finset (Vec m)))
      (fun x _ => mem_univ _)
    simp only [hconst] at h
    rw [Finset.sum_const] at h
    simp [ZMod.card] at h ⊢
    exact h
  have hmd : m ≤ d := by
    by_contra hcon
    push_neg at hcon
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · rw [h0, mul_zero] at htot
        have : (0 : ℕ) < 2 ^ d := Nat.two_pow_pos d
        omega
      · exact h0
    have h2 : (2 : ℕ) ^ d < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hcon
    have h3 : (2 : ℕ) ^ m ≤ 2 ^ m * c := Nat.le_mul_of_pos_right _ hc1
    omega
  have heq : (2 : ℕ) ^ m * c = 2 ^ m * 2 ^ (d - m) := by
    rw [← htot, ← pow_add]
    congr 1
    omega
  rw [hconst b]
  exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos m) heq
