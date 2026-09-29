-- Prove2me | solution 1 for NeuralCodePlotkinTightness.ip_update
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:46:11.967885+00:00
-- url     : https://prove2.me/submissions/2b6f4869-0601-42a3-a361-c1def75c8022

-- Sol generated from Novelty/NeuralCodePlotkinTightness.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Definitions.Def_Novelty_NeuralCodePlotkinTightness

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



lemma bit_not (b : Bool) : bit (!b) = bit b + 1 := by cases b <;> decide














/-! ## Tightness -/





open NeuralCodePlotkinTightness in
theorem solution{k : ℕ} (a x : Fin k → Bool) (j : Fin k) (ha : a j = true) :
    ip a (Function.update x j (!x j)) = ip a x + 1 := by
  classical
  unfold ip
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
      ← Finset.add_sum_erase Finset.univ (fun i => bit (a i) * bit (x i))
        (Finset.mem_univ j)]
  have hrest : ∀ i ∈ (Finset.univ : Finset (Fin k)).erase j,
      bit (a i) * bit (Function.update x j (!x j) i) = bit (a i) * bit (x i) := by
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [Finset.sum_congr rfl hrest, Function.update_self, ha, bit_not]
  simp only [bit, if_true]
  ring
