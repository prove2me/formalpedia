-- Prove2me | Theorems.Thm_NeuralCodePlotkinTightness_card_filter_last_le
-- name    : NeuralCodePlotkinTightness.card_filter_last_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:11:21.4919+00:00
-- url     : https://prove2.me/theorems/d2b0838e-85b5-4c36-905e-96489b2fdd5e
-- title:
--   Codewords of a `d`-separated codebook that agree on the last neuron stay
-- statement:
--   Codewords of a `d`-separated codebook that agree on the last neuron stay
--   `d`-separated, and remain distinct, after that neuron is deleted.
--
--   ```lean
--   theorem NeuralCodePlotkinTightness.card_filter_last_le{N d : ℕ} {C : Finset (NeuralCode (N + 1))}
--       (hC : Separated d C) (b : Bool) (hd : 1 ≤ d) :
--       (C.filter fun x => x (Fin.last N) = b).card ≤ maxCodeSize N d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NeuralCodePlotkinTightness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NeuralCodePlotkinTightness.lean#L37

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

theorem NeuralCodePlotkinTightness.card_filter_last_le{N d : ℕ} {C : Finset (NeuralCode (N + 1))}
    (hC : Separated d C) (b : Bool) (hd : 1 ≤ d) :
    (C.filter fun x => x (Fin.last N) = b).card ≤ maxCodeSize N d := by sorry
