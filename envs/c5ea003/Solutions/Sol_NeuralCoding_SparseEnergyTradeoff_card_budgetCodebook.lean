-- Prove2me | solution 1 for NeuralCoding.SparseEnergyTradeoff.card_budgetCodebook
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T02:11:49.072212+00:00
-- url     : https://prove2.me/submissions/af6c2ad2-8027-4484-ae11-b83fa438b900

-- Sol generated from Novelty/SparseEnergyTradeoff.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCoding
import Definitions.Def_Novelty_SparseEnergyTradeoff
import Theorems.Thm_NeuralCoding_card_sparse

/-!
# Sparse neural coding: exact capacity and an energy–information bound

A binary pattern on `N` neurons has energy equal to its Hamming weight.  This
file studies the codebook consisting of all patterns using at most `k` spikes.
Its size is exactly the Hamming-ball volume

`∑ j ∈ range (k+1), N.choose j`.

For exactly `k` spikes, the number of concepts is `N.choose k`.  The central
energy theorem proves that this capacity is at most `N^k`; consequently its
information content per spike is at most `log₂ N`.  Thus fixed sparsity gives
polynomial raw capacity while information per unit energy grows only
logarithmically with population size.  The result also applies directly to a
one-percent budget by substituting `k = N / 100`.
-/

open NeuralCoding.SparseEnergyTradeoff

open Finset
open NeuralCoding










open NeuralCoding.SparseEnergyTradeoff in
theorem solution(N k : ℕ) :
    (budgetCodebook N k).card = ∑ j ∈ Finset.range (k + 1), N.choose j := by
  unfold budgetCodebook
  calc
    (Finset.univ.filter (fun c : NeuralCode N => weight c ≤ k)).card =
        (Finset.univ.filter (fun c : NeuralCode N => weight c ∈ Finset.range (k + 1))).card := by
      congr 1
      ext c
      simp
    _ = ∑ j ∈ Finset.range (k + 1),
          (Finset.univ.filter (fun c : NeuralCode N => weight c = j)).card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
    _ = ∑ j ∈ Finset.range (k + 1), N.choose j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [NeuralCoding.card_sparse]
