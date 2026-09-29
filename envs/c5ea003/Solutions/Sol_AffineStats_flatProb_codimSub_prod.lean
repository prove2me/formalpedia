-- Prove2me | solution 1 for AffineStats.flatProb_codimSub_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:27.062121+00:00
-- url     : https://prove2.me/submissions/dd58de46-a8f4-4906-8595-dd869e543ce1

-- Sol generated from Applications/AffineSubspaceStats/ExactProduct.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Theorems.Thm_AffineStats_card_surj_dirs
import Theorems.Thm_AffineStats_card_surj_tuples
import Theorems.Thm_AffineStats_flatProb_codimSub_eq
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












open AffineStats in
theorem solution(hmn : m ≤ n) (hmd : m ≤ d) :
    flatProb n d (codimSub n hmn) (2 ^ (d - m))
      = ∏ i : Fin m, (1 - (2 : ℚ) ^ (i : ℕ) / 2 ^ d) := by
  classical
  rw [flatProb_codimSub_eq hmn hmd]
  have hcount := card_surj_dirs hmn d
  rw [card_surj_tuples hmd] at hcount
  -- pass to `ℚ`
  have hQ : (2 : ℚ) ^ (m * d) *
      ((univ.filter fun v : Fin d → Vec n =>
        Function.Surjective (Lmap fun i => proj hmn (v i))).card : ℚ)
      = ((∏ i : Fin m, (2 ^ d - 2 ^ (i : ℕ)) : ℕ) : ℚ) * 2 ^ (n * d) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℚ)) hcount
  have hprodcast : ((∏ i : Fin m, (2 ^ d - 2 ^ (i : ℕ)) : ℕ) : ℚ)
      = ∏ i : Fin m, ((2 : ℚ) ^ d - 2 ^ (i : ℕ)) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hle : (2 : ℕ) ^ (i : ℕ) ≤ 2 ^ d :=
      Nat.pow_le_pow_right (by norm_num) (le_trans (le_of_lt i.isLt) hmd)
    push_cast [Nat.cast_sub hle]
    ring
  rw [hprodcast] at hQ
  have hne : ((2 : ℚ) ^ (n * d)) ≠ 0 := by positivity
  have hne2 : ((2 : ℚ) ^ (m * d)) ≠ 0 := by positivity
  have hsplit : ∏ i : Fin m, (1 - (2 : ℚ) ^ (i : ℕ) / 2 ^ d)
      = (∏ i : Fin m, ((2 : ℚ) ^ d - 2 ^ (i : ℕ))) / 2 ^ (m * d) := by
    have h1 : ∀ i : Fin m, (1 - (2 : ℚ) ^ (i : ℕ) / 2 ^ d) = ((2 : ℚ) ^ d - 2 ^ (i : ℕ)) / 2 ^ d := by
      intro i; field_simp
    rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Nat.mul_comm d m]
  rw [hsplit]
  field_simp
  linarith [hQ]
