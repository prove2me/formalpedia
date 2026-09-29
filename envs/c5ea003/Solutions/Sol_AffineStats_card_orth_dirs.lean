-- Prove2me | solution 1 for AffineStats.card_orth_dirs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:23:24.946469+00:00
-- url     : https://prove2.me/submissions/66e3351e-ec49-4002-b557-f7b2339d4eac

-- Sol generated from Applications/AffineSubspaceStats/CodimSubspace.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Theorems.Thm_AffineStats_card_Vec
import Theorems.Thm_AffineStats_card_filter_involutive
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
theorem solution(hmn : m ≤ n) (a : Vec m) (ha : a ≠ 0) :
    2 ^ d * (univ.filter fun v : Fin d → Vec n =>
        ∀ i, ∑ j, a j * proj hmn (v i) j = 0).card = 2 ^ (n * d) := by
  set g : Vec n → ZMod 2 := fun x => ∑ j, a j * proj hmn x j with hg
  obtain ⟨j₀, hj₀⟩ : ∃ j, a j = 1 := by
    by_contra hcon
    push_neg at hcon
    refine ha (funext fun j => ?_)
    have h1 : ∀ t : ZMod 2, t ≠ 1 → t = 0 := by decide
    simpa using h1 (a j) (hcon j)
  set u : Vec n := fun k => if Fin.castLE hmn j₀ = k then (1 : ZMod 2) else 0 with hu
  have hgu : g u = 1 := by simp [hg, hu, proj, Fin.castLE_inj, hj₀]
  have hadd : ∀ x : Vec n, g (x + u) = g x + g u := by
    intro x
    simp [hg, proj, mul_add, Finset.sum_add_distrib]
  have hhalf : 2 * (univ.filter fun x : Vec n => g x = 0).card = 2 ^ n := by
    have hinv := card_filter_involutive (α := Vec n) (fun x => g x = 0) (fun x => x + u)
      (fun x => by simp [add_assoc, vadd_self]) (by
        intro x
        show g (x + u) = 0 ↔ ¬ (g x = 0)
        rw [hadd x, hgu]
        generalize g x = t
        revert t
        decide)
    rw [hinv, card_Vec]
  have hprod : (univ.filter fun v : Fin d → Vec n => ∀ i, g (v i) = 0).card
      = (univ.filter fun x : Vec n => g x = 0).card ^ d := by
    rw [show (univ.filter fun v : Fin d → Vec n => ∀ i, g (v i) = 0)
        = Fintype.piFinset (fun _ : Fin d => univ.filter fun x : Vec n => g x = 0) from by
      ext v; simp [Fintype.mem_piFinset]]
    rw [Fintype.card_piFinset]
    simp
  rw [show (univ.filter fun v : Fin d → Vec n => ∀ i, ∑ j, a j * proj hmn (v i) j = 0)
      = univ.filter fun v : Fin d → Vec n => ∀ i, g (v i) = 0 from rfl, hprod,
    ← mul_pow, hhalf, ← pow_mul, Nat.mul_comm]
