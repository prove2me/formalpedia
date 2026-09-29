-- Prove2me | solution 1 for NeuralCodePlotkinTightness.maxCodeSize_shorten
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:54:11.570355+00:00
-- url     : https://prove2.me/submissions/9bcfaa40-28a4-460e-beac-f2e5563265de

-- Sol generated from Novelty/NeuralCodePlotkinTightness.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Definitions.Def_Novelty_NeuralCodePlotkinTightness
import Theorems.Thm_NeuralCodeCapacity_exists_maxCodeSize
import Theorems.Thm_NeuralCodePlotkinTightness_card_filter_last_le

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
theorem solution(N d : ℕ) (hd : 1 ≤ d) :
    maxCodeSize (N + 1) d ≤ 2 * maxCodeSize N d := by
  classical
  obtain ⟨C, hC, hcard⟩ := exists_maxCodeSize (N + 1) d
  have hfalse : (C.filter fun x => ¬ (x (Fin.last N) = true))
      = (C.filter fun x => x (Fin.last N) = false) := by
    apply Finset.filter_congr
    intro x _
    simp
  have hsplit :
      (C.filter fun x => x (Fin.last N) = true).card
        + (C.filter fun x => x (Fin.last N) = false).card = C.card := by
    rw [← hfalse]
    exact Finset.card_filter_add_card_filter_not _
  have h1 := card_filter_last_le hC true hd
  have h0 := card_filter_last_le hC false hd
  omega
