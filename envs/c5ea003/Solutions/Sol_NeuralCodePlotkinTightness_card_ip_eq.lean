-- Prove2me | solution 1 for NeuralCodePlotkinTightness.card_ip_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:48:53.50055+00:00
-- url     : https://prove2.me/submissions/e41663e3-31be-489e-b262-5cc411e43141

-- Sol generated from Novelty/NeuralCodePlotkinTightness.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Definitions.Def_Novelty_NeuralCodePlotkinTightness
import Theorems.Thm_NeuralCodePlotkinTightness_ip_update

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
theorem solution{k : ℕ} {u : Fin k → Bool} (hu : ∃ j, u j = true) (c : ZMod 2) :
    ((Finset.univ : Finset (Fin k → Bool)).filter fun x => ip u x = c).card
      = 2 ^ k / 2 := by
  classical
  obtain ⟨j, hj⟩ := hu
  -- flipping the `j`-th bit is a bijection between the two level sets
  have hbij : ∀ c : ZMod 2,
      ((Finset.univ : Finset (Fin k → Bool)).filter fun x => ip u x = c).card
        = ((Finset.univ : Finset (Fin k → Bool)).filter fun x => ip u x = c + 1).card := by
    intro c
    refine Finset.card_nbij' (fun x => Function.update x j (!x j))
      (fun x => Function.update x j (!x j)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [ip_update u x j hj, hx]
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [ip_update u x j hj, hx]
      generalize c = z
      revert z
      decide
    · intro x _
      funext i
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h]
    · intro x _
      funext i
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h]
  -- the two level sets partition all strings
  have hsplit :
      ((Finset.univ : Finset (Fin k → Bool)).filter fun x => ip u x = 0).card
        + ((Finset.univ : Finset (Fin k → Bool)).filter fun x => ip u x = 1).card
        = 2 ^ k := by
    have hcompl : ((Finset.univ : Finset (Fin k → Bool)).filter fun x => ip u x = 1)
        = ((Finset.univ : Finset (Fin k → Bool)).filter fun x => ¬ (ip u x = 0)) := by
      refine Finset.filter_congr fun x _ => ?_
      generalize ip u x = z
      revert z
      decide
    rw [hcompl, Finset.card_filter_add_card_filter_not]
    simp
  have h01 := hbij 0
  have h0 : (0 : ZMod 2) + 1 = 1 := by decide
  rw [h0] at h01
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl <;> omega
