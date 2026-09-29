-- Prove2me | solution 1 for AffineStats.surj_iff_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:36:32.549871+00:00
-- url     : https://prove2.me/submissions/18b423f9-7411-4ae2-acc8-733f72e274fe

-- Sol generated from Applications/AffineSubspaceStats/ExactProduct.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Theorems.Thm_AffineStats_exists_orth_of_not_surjective
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
theorem solution(w : Fin d → Vec m) :
    Function.Surjective (Lmap w) ↔
      LinearIndependent (ZMod 2) (fun j : Fin m => (fun i => w i j : Vec d)) := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hs g hg j₀
    have hzero : ∀ i : Fin d, ∑ j, g j * w i j = 0 := by
      intro i
      have h := congrFun hg i
      simpa [Finset.sum_apply, mul_comm] using h
    obtain ⟨y, hy⟩ := hs (fun j => if j₀ = j then (1 : ZMod 2) else 0)
    have hcalc : ∑ j, g j * (Lmap w y) j = 0 := by
      have hswap : ∑ j, g j * (Lmap w y) j = ∑ i, y i * (∑ j, g j * w i j) := by
        simp only [Lmap, Fintype.linearCombination, LinearMap.coe_mk, AddHom.coe_mk,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      rw [hswap]
      simp [hzero]
    rw [hy] at hcalc
    simpa using hcalc
  · intro hli
    by_contra hns
    obtain ⟨a, ha0, ha⟩ := exists_orth_of_not_surjective w hns
    refine ha0 (funext fun j => ?_)
    have hsum : ∑ j, a j • (fun i => w i j : Vec d) = 0 := by
      funext i
      simpa [Finset.sum_apply, mul_comm] using ha i
    simpa using hli a hsum j
