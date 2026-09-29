-- Prove2me | solution 1 for AffineStats.card_surj_tuples
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:38:45.437284+00:00
-- url     : https://prove2.me/submissions/4ef0d631-f826-41e3-bd10-6c9579b65497

-- Sol generated from Applications/AffineSubspaceStats/ExactProduct.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Theorems.Thm_AffineStats_surj_iff_linearIndependent
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
theorem solution(hmd : m ≤ d) :
    (univ.filter fun w : Fin d → Vec m => Function.Surjective (Lmap w)).card
      = ∏ i : Fin m, (2 ^ d - 2 ^ (i : ℕ)) := by
  classical
  have hfr : Module.finrank (ZMod 2) (Vec d) = d := by simp [Vec]
  have hcard := card_linearIndependent (K := ZMod 2) (V := Vec d) (k := m)
    (by omega : m ≤ Module.finrank (ZMod 2) (Vec d))
  rw [hfr, ZMod.card] at hcard
  have hequiv : {w : Fin d → Vec m // Function.Surjective (Lmap w)}
      ≃ {s : Fin m → Vec d // LinearIndependent (ZMod 2) s} :=
    Equiv.subtypeEquiv (Equiv.piComm _) fun w => by
      simpa [Equiv.piComm] using surj_iff_linearIndependent w
  have h1 : Nat.card {w : Fin d → Vec m // Function.Surjective (Lmap w)}
      = Nat.card {s : Fin m → Vec d // LinearIndependent (ZMod 2) s} := Nat.card_congr hequiv
  rw [hcard] at h1
  rw [← h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
