-- Prove2me | solution 1 for NeuralCodePlotkinTightness.hadamard_capacity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:55:37.093537+00:00
-- url     : https://prove2.me/submissions/e1a6b98c-118c-4447-8ee2-3811a97b4757

-- Sol generated from Novelty/NeuralCodePlotkinTightness.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Definitions.Def_Novelty_NeuralCodePlotkinTightness
import Theorems.Thm_NeuralCodeCapacity_card_le_maxCodeSize
import Theorems.Thm_NeuralCodeCapacity_plotkin_bound_maxCodeSize
import Theorems.Thm_NeuralCodePlotkinTightness_affineWord_dist
import Theorems.Thm_NeuralCodePlotkinTightness_card_affineCode
import Theorems.Thm_NeuralCodePlotkinTightness_maxCodeSize_shorten

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



/-- **Plotkin bound at the boundary.**  A population of `2d` neurons whose
concepts must differ on at least `d` neurons represents at most `4d` concepts.
(The plain Plotkin inequality degenerates at `N = 2d`; shortening on one neuron
recovers the bound.) -/
theorem plotkin_boundary (d : ℕ) (hd : 1 ≤ d) : maxCodeSize (2 * d) d ≤ 4 * d := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hshort : maxCodeSize (2 * (m + 1)) (m + 1) ≤ 2 * maxCodeSize (2 * m + 1) (m + 1) := by
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring]
    exact maxCodeSize_shorten _ _ (by omega)
  have hplot := plotkin_bound_maxCodeSize (N := 2 * m + 1) (d := m + 1) (by omega)
  have he : 2 * (m + 1) - (2 * m + 1) = 1 := by omega
  rw [he, Nat.mul_one] at hplot
  omega

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


/-- The affine code is `2 ^ k / 2`-separated: its concepts survive
`2 ^ k / 2 - 1` misfirings. -/
theorem affineCode_separated (k : ℕ) : Separated (2 ^ k / 2) (affineCode k) := by
  classical
  intro y hy z hz hyz
  simp only [affineCode, Finset.mem_image, Finset.mem_univ, true_and] at hy hz
  obtain ⟨⟨a, b⟩, rfl⟩ := hy
  obtain ⟨⟨a', b'⟩, rfl⟩ := hz
  have hne : ((a, b) : (Fin k → Bool) × Bool) ≠ (a', b') := fun hcon => hyz (by rw [hcon])
  rw [hammingDist_comp_equiv (strEquiv k).symm (affineWord a b) (affineWord a' b')]
  exact affineWord_dist a a' b b' hne


/-! ## Tightness -/





open NeuralCodePlotkinTightness in
theorem solution(m : ℕ) :
    maxCodeSize (2 ^ (m + 1)) (2 ^ m) = 2 ^ (m + 2) := by
  have hN : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
  refine le_antisymm ?_ ?_
  · have := plotkin_boundary (2 ^ m) (Nat.one_le_two_pow)
    rw [← hN] at this
    calc maxCodeSize (2 ^ (m + 1)) (2 ^ m) ≤ 4 * 2 ^ m := this
      _ = 2 ^ (m + 2) := by ring
  · have hhalf : 2 ^ (m + 1) / 2 = 2 ^ m := by
      rw [hN, Nat.mul_div_cancel_left _ (by norm_num)]
    have hsep := affineCode_separated (m + 1)
    rw [hhalf] at hsep
    have := card_le_maxCodeSize hsep
    rw [card_affineCode (m + 1) (by omega)] at this
    calc (2 : ℕ) ^ (m + 2) = 2 ^ (m + 1 + 1) := by ring_nf
      _ ≤ maxCodeSize (2 ^ (m + 1)) (2 ^ m) := this
