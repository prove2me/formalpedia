-- Prove2me | Definitions.Def_Novelty_NeuralCodePlotkinTightness
-- name    : Novelty_NeuralCodePlotkinTightness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:33:36.48459+00:00
-- url     : https://prove2.me/theorems/717fc831-e1ac-405e-826e-d53b3c7d0798
-- title:
--   Aether Catalog definitions — Novelty_NeuralCodePlotkinTightness
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.NeuralCodePlotkinTightness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/NeuralCodePlotkinTightness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds

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

namespace NeuralCodePlotkinTightness

open Finset NeuralCodeCapacity

/-! ## Shortening: `A(N+1, d) ≤ 2 * A(N, d)` -/




/-! ## The affine (Hadamard) neural code

Neurons are indexed by the `2 ^ k` binary strings of length `k`; a concept is a
pair `(a, b)` with `a` a string of length `k` and `b` a bit, and the pattern it
evokes fires neuron `x` exactly when the affine form `⟨a, x⟩ + b` is odd. -/

/-- A bit read as an element of `ℤ/2`. -/
def bit (b : Bool) : ZMod 2 := if b then 1 else 0



/-- The `ℤ/2`-valued inner product of two binary strings. -/
def ip {k : ℕ} (a x : Fin k → Bool) : ZMod 2 := ∑ i, bit (a i) * bit (x i)





/-- The codeword of the concept `(a, b)`: neuron `x` fires iff `⟨a,x⟩ + b` is
odd. -/
def affineWord {k : ℕ} (a : Fin k → Bool) (b : Bool) (x : Fin k → Bool) : Bool :=
  decide (ip a x + bit b = 1)



/-- A relabelling of the `2 ^ k` neurons by the binary strings of length `k`. -/
noncomputable def strEquiv (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  Fintype.equivFinOfCardEq (by simp)


/-- The **affine neural code**: the codebook of all affine forms, transported to
a population of `2 ^ k` neurons. -/
noncomputable def affineCode (k : ℕ) : Finset (NeuralCode (2 ^ k)) :=
  Finset.image (fun p : (Fin k → Bool) × Bool =>
    (affineWord p.1 p.2 ∘ (strEquiv k).symm : NeuralCode (2 ^ k))) Finset.univ



/-! ## Tightness -/




end NeuralCodePlotkinTightness


