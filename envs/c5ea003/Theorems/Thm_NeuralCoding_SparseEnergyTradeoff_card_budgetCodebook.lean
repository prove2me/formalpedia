-- Prove2me | Theorems.Thm_NeuralCoding_SparseEnergyTradeoff_card_budgetCodebook
-- name    : NeuralCoding.SparseEnergyTradeoff.card_budgetCodebook
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:12:10.87889+00:00
-- url     : https://prove2.me/theorems/8c3fef11-64e9-49dc-9482-8a68d4bef2fe
-- title:
--   The exact capacity under a spike budget is the lower binomial sum.
-- statement:
--   The exact capacity under a spike budget is the lower binomial sum.
--
--   ```lean
--   theorem NeuralCoding.SparseEnergyTradeoff.card_budgetCodebook(N k : ℕ) :
--       (budgetCodebook N k).card = ∑ j ∈ Finset.range (k + 1), N.choose j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SparseEnergyTradeoff.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SparseEnergyTradeoff.lean#L33

-- Thm stub generated from Novelty/SparseEnergyTradeoff.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCoding
import Definitions.Def_Novelty_SparseEnergyTradeoff

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

theorem NeuralCoding.SparseEnergyTradeoff.card_budgetCodebook(N k : ℕ) :
    (budgetCodebook N k).card = ∑ j ∈ Finset.range (k + 1), N.choose j := by sorry
