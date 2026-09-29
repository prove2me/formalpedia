-- Prove2me | solution 1 for AffineStats.card_surj_dirs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:36:32.022435+00:00
-- url     : https://prove2.me/submissions/9a4bda0f-ef14-4150-9c18-37cc10b551e1

-- Sol generated from Applications/AffineSubspaceStats/ExactProduct.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Theorems.Thm_AffineStats_card_Vec
import Theorems.Thm_AffineStats_card_proj_fiber_eq
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



/-- The projection is `2^{n-m}`-to-one: `2^m` times the fiber size is `2^n`. -/
lemma card_proj_fiber_mul (hmn : m ≤ n) :
    2 ^ m * (univ.filter fun x : Vec n => proj hmn x = 0).card = 2 ^ n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := fun x : Vec n => proj hmn x)
    (s := univ) (t := (univ : Finset (Vec m))) (fun x _ => mem_univ _)
  rw [Finset.sum_congr rfl (fun w _ => card_proj_fiber_eq hmn w), Finset.sum_const,
    smul_eq_mul, Finset.card_univ, card_Vec, Finset.card_univ, card_Vec] at h
  omega

/-- Fibers of the induced map on direction tuples. -/
lemma card_tuple_fiber (hmn : m ≤ n) (w : Fin d → Vec m) :
    (univ.filter fun v : Fin d → Vec n => (fun i => proj hmn (v i)) = w).card
      = (univ.filter fun x : Vec n => proj hmn x = 0).card ^ d := by
  classical
  rw [show (univ.filter fun v : Fin d → Vec n => (fun i => proj hmn (v i)) = w)
      = Fintype.piFinset (fun i => univ.filter fun x : Vec n => proj hmn x = w i) from by
    ext v; simp [Fintype.mem_piFinset, funext_iff]]
  rw [Fintype.card_piFinset]
  simp [card_proj_fiber_eq hmn]








open AffineStats in
theorem solution(hmn : m ≤ n) (d : ℕ) :
    2 ^ (m * d) *
        (univ.filter fun v : Fin d → Vec n =>
          Function.Surjective (Lmap fun i => proj hmn (v i))).card
      = (univ.filter fun w : Fin d → Vec m =>
          Function.Surjective (Lmap w)).card * 2 ^ (n * d) := by
  classical
  set F := (univ.filter fun x : Vec n => proj hmn x = 0).card with hF
  set W := (univ.filter fun w : Fin d → Vec m => Function.Surjective (Lmap w)) with hW
  have hpart : (univ.filter fun v : Fin d → Vec n =>
      Function.Surjective (Lmap fun i => proj hmn (v i))).card = W.card * F ^ d := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun v : Fin d → Vec n => fun i => proj hmn (v i))
      (s := univ.filter fun v : Fin d → Vec n =>
        Function.Surjective (Lmap fun i => proj hmn (v i))) (t := W)
      (fun v hv => by
        simp only [hW, Finset.mem_coe, mem_filter, mem_univ, true_and]
        exact (mem_filter.1 hv).2)]
    refine (Finset.sum_congr rfl (fun w hw => ?_)).trans (by
      rw [Finset.sum_const, smul_eq_mul])
    have hwsurj : Function.Surjective (Lmap w) := by simpa [hW] using hw
    rw [show ((univ.filter fun v : Fin d → Vec n =>
        Function.Surjective (Lmap fun i => proj hmn (v i))).filter
          fun v => (fun i => proj hmn (v i)) = w)
        = univ.filter (fun v : Fin d → Vec n => (fun i => proj hmn (v i)) = w) from by
      ext v
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hwsurj, h⟩⟩]
    exact card_tuple_fiber hmn w
  have h1 : (2 : ℕ) ^ (m * d) * F ^ d = 2 ^ (n * d) := by
    rw [pow_mul, pow_mul, ← mul_pow, card_proj_fiber_mul hmn]
  rw [hpart, show (2 : ℕ) ^ (m * d) * (W.card * F ^ d) = W.card * (2 ^ (m * d) * F ^ d) from by
    ring, h1]
