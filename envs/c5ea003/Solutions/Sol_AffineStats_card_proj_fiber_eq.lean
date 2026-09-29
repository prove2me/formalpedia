-- Prove2me | solution 1 for AffineStats.card_proj_fiber_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:34:01.518339+00:00
-- url     : https://prove2.me/submissions/afa3a1b8-fb21-4e79-bfd5-47504b607c0d

-- Sol generated from Applications/AffineSubspaceStats/ExactProduct.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Theorems.Thm_AffineStats_vadd_self
/-
# Affine subspace statistics in `𝔽₂ⁿ`: the exact value of the codimension-`m` construction

This file completes the analysis of the codimension-`m` lower-bound construction begun in
`Catalog/Applications/AffineSubspaceStats/CodimSubspace.lean`.  There it was shown that a
random affine `d`-cube meets the codimension-`m` subspace `A ⊆ 𝔽₂ⁿ` in exactly `2^{d-m}`
points *iff* the projected directions span `𝔽₂^m` (for `m ≤ d`), and that this happens with
probability at least `1 - (2^m - 1)/2^d`.

Here we compute the probability exactly:

`P[|F ∩ A| = 2^{d-m}] = ∏_{i<m} (1 - 2^{i-d})`,

for all `n ≥ m` and `d ≥ m`.  With `k = d - m` the right-hand side is
`∏_{t=k+1}^{d} (1 - 2^{-t})`, the exact value of the classical lower-bound construction for
the affine subspace statistics problem; in particular it is `≥ 1 - 2^{-k}` and tends to
`1 - 2^{-k}` from above only up to the explicit correction computed here.

The proof has three ingredients:

* the fibers of the coordinate projection `π : 𝔽₂ⁿ → 𝔽₂^m` all have the same size, so the
  count of good direction tuples in `𝔽₂ⁿ` reduces to the count of good tuples in `𝔽₂^m`
  (`card_surj_dirs`);
* `y ↦ ∑ yᵢwᵢ` is surjective iff the transposed family of `m` vectors of `𝔽₂^d` is linearly
  independent (`surj_iff_linearIndependent`);
* the number of linearly independent `m`-tuples in `𝔽₂^d` is `∏_{i<m}(2^d - 2^i)`
  (Mathlib's `card_linearIndependent`).
-/

open AffineStats

open Finset


variable {n m d : ℕ}

lemma proj_add (hmn : m ≤ n) (x y : Vec n) : proj hmn (x + y) = proj hmn x + proj hmn y := rfl











open AffineStats in
theorem solution(hmn : m ≤ n) (w : Vec m) :
    (univ.filter fun x : Vec n => proj hmn x = w).card
      = (univ.filter fun x : Vec n => proj hmn x = 0).card := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Vec n, proj hmn x₀ = w := by
    refine ⟨fun i => if h : i.val < m then w ⟨i.val, h⟩ else 0, ?_⟩
    funext j
    simp [proj, Fin.castLE]
  have hcancel : ∀ x : Vec n, x + x₀ + x₀ = x := by
    intro x; rw [add_assoc, vadd_self, add_zero]
  refine Finset.card_nbij' (fun x => x + x₀) (fun z => z + x₀) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at ha ⊢
    rw [proj_add hmn, ha, hx₀, vadd_self]
  · intro a ha
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at ha ⊢
    rw [proj_add hmn, ha, hx₀, zero_add]
  · intro a _; exact hcancel a
  · intro a _; exact hcancel a
