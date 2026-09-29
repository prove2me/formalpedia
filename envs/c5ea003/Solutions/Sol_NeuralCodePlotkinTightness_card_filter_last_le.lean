-- Prove2me | solution 1 for NeuralCodePlotkinTightness.card_filter_last_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:52:40.292232+00:00
-- url     : https://prove2.me/submissions/0a0859b1-3669-419a-86b5-8f068048133a

-- Sol generated from Novelty/NeuralCodePlotkinTightness.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Definitions.Def_Novelty_NeuralCodePlotkinTightness
import Theorems.Thm_NeuralCodeCapacity_card_le_maxCodeSize
import Theorems.Thm_NeuralCodeCapacity_dist_punct

/-!
# Neural Coding: tightness of the Plotkin bound (Hadamard populations)

`Catalog/Novelty/NeuralCodeCapacityBounds.lean` proves the Plotkin bound: a
`d`-separated codebook on `N` neurons with `N < 2d` satisfies
`|C| * (2d - N) ≤ 2d`.  At the boundary `N = 2d` that inequality degenerates,
and the correct statement `A(2d, d) ≤ 4d` needs a *shortening* argument.  This
file proves that bound and shows it is **attained** whenever `2d` is a power of
two, by the affine (first-order Reed–Muller / Hadamard) neural code.

## Main results

* `maxCodeSize_shorten` — shortening on one neuron: `A(N+1, d) ≤ 2 * A(N, d)`.
* `plotkin_boundary` — the boundary Plotkin bound `A(2d, d) ≤ 4d`.
* `affineCode_separated`, `card_affineCode` — the affine code on `2 ^ (m+1)`
  neurons has `2 ^ (m+2)` codewords, pairwise at Hamming distance at least
  `2 ^ m`.
* `hadamard_capacity` — **Plotkin is tight**: `A(2 ^ (m+1), 2 ^ m) = 2 ^ (m+2)`.
  A population of `N = 2 ^ (m+1)` neurons that must tolerate `2 ^ m - 1`
  misfirings represents exactly `2N` concepts, realised by the affine code.
* `hadamard_capacity_half` — the same statement written as
  `A(N, N/2) = 2N` for `N` a power of two.
* `hadamard_capacity_rate` — the corresponding rate statement.

The smallest instances agree with the exhaustive search recorded in
`ComputationalEvidence.md`: `A(2,1) = 4` and `A(4,2) = 8`.
-/

open NeuralCodePlotkinTightness

open Finset NeuralCodeCapacity

/-! ## Shortening: `A(N+1, d) ≤ 2 * A(N, d)` -/




/-! ## The affine (Hadamard) neural code

Neurons are indexed by the `2 ^ k` binary strings of length `k`; a concept is a
pair `(a, b)` with `a` a string of length `k` and `b` a bit, and the pattern it
evokes fires neuron `x` exactly when the affine form `⟨a, x⟩ + b` is odd. -/

















/-! ## Tightness -/





open NeuralCodePlotkinTightness in
theorem solution{N d : ℕ} {C : Finset (NeuralCode (N + 1))}
    (hC : Separated d C) (b : Bool) (hd : 1 ≤ d) :
    (C.filter fun x => x (Fin.last N) = b).card ≤ maxCodeSize N d := by
  classical
  set D := C.filter fun x => x (Fin.last N) = b with hD
  have hlast : ∀ x ∈ D, x (Fin.last N) = b := by
    intro x hx; exact (Finset.mem_filter.mp hx).2
  have hmem : ∀ x ∈ D, x ∈ C := fun x hx => (Finset.mem_filter.mp hx).1
  have hdist : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → d ≤ hammingDist (punct x) (punct y) := by
    intro x hx y hy hxy
    have h1 := hC x (hmem x hx) y (hmem y hy) hxy
    have h2 := dist_punct x y
    rw [hlast x hx, hlast y hy] at h2
    simp at h2
    omega
  have hinj : Set.InjOn (punct (N := N)) (D : Set (NeuralCode (N + 1))) := by
    intro x hx y hy hxy
    by_contra hne
    have := hdist x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hne
    rw [hxy, hammingDist_self] at this
    omega
  have hsep : Separated d (D.image punct) := by
    intro u hu v hv huv
    simp only [Finset.mem_image] at hu hv
    obtain ⟨x, hx, rfl⟩ := hu
    obtain ⟨y, hy, rfl⟩ := hv
    exact hdist x hx y hy (fun h => huv (by rw [h]))
  have := card_le_maxCodeSize hsep
  rwa [Finset.card_image_of_injOn hinj] at this
