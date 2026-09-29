-- Prove2me | Theorems.Thm_NeuralCodePlotkinTightness_ip_update
-- name    : NeuralCodePlotkinTightness.ip_update
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:11:10.399477+00:00
-- url     : https://prove2.me/theorems/314a8c39-390e-4127-a1ff-63e05811c52b
-- title:
--   Flipping the `j`-th bit of `x` changes `⟨a, x⟩` exactly when `a j` is set.
-- statement:
--   Flipping the `j`-th bit of `x` changes `⟨a, x⟩` exactly when `a j` is set.
--
--   ```lean
--   theorem NeuralCodePlotkinTightness.ip_update{k : ℕ} (a x : Fin k → Bool) (j : Fin k) (ha : a j = true) :
--       ip a (Function.update x j (!x j)) = ip a x + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NeuralCodePlotkinTightness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NeuralCodePlotkinTightness.lean#L133

-- Thm stub generated from Novelty/NeuralCodePlotkinTightness.lean
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

theorem NeuralCodePlotkinTightness.ip_update{k : ℕ} (a x : Fin k → Bool) (j : Fin k) (ha : a j = true) :
    ip a (Function.update x j (!x j)) = ip a x + 1 := by sorry
