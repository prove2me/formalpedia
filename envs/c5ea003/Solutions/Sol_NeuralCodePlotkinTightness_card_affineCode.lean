-- Prove2me | solution 1 for NeuralCodePlotkinTightness.card_affineCode
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:52:39.791052+00:00
-- url     : https://prove2.me/submissions/c33e102d-6669-4362-aa65-7f6280bdf4fe

-- Sol generated from Novelty/NeuralCodePlotkinTightness.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Definitions.Def_Novelty_NeuralCodePlotkinTightness
import Theorems.Thm_NeuralCodePlotkinTightness_affineWord_dist

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













/-- Hamming distance is invariant under a relabelling of the neurons. -/
lemma hammingDist_comp_equiv {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (f g : β → Bool) :
    hammingDist (f ∘ e) (g ∘ e) = hammingDist f g := by
  classical
  rw [hammingDist, hammingDist]
  refine Finset.card_nbij' (fun a => e a) (fun b => e.symm b) ?_ ?_ ?_ ?_ <;>
    intro x hx <;> simp_all




/-! ## Tightness -/





open NeuralCodePlotkinTightness in
theorem solution(k : ℕ) (hk : 1 ≤ k) : (affineCode k).card = 2 ^ (k + 1) := by
  classical
  have hpos : 0 < 2 ^ k / 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [show (2 : ℕ) ^ (m + 1) = 2 ^ m * 2 by ring, Nat.mul_div_cancel _ (by norm_num)]
    positivity
  have hinj : Function.Injective (fun p : (Fin k → Bool) × Bool =>
      (affineWord p.1 p.2 ∘ (strEquiv k).symm : NeuralCode (2 ^ k))) := by
    intro p q hpq
    by_contra hne
    have hd := affineWord_dist p.1 q.1 p.2 q.2 (fun hcon => hne
      (Prod.ext (congrArg Prod.fst hcon) (congrArg Prod.snd hcon)))
    rw [← hammingDist_comp_equiv (strEquiv k).symm (affineWord p.1 p.2) (affineWord q.1 q.2),
      show (affineWord p.1 p.2 ∘ (strEquiv k).symm) = (affineWord q.1 q.2 ∘ (strEquiv k).symm)
        from hpq, hammingDist_self] at hd
    omega
  rw [affineCode, Finset.card_image_of_injective _ hinj]
  simp [pow_succ]
