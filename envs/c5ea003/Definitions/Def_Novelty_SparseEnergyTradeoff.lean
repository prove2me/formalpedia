-- Prove2me | Definitions.Def_Novelty_SparseEnergyTradeoff
-- name    : Novelty_SparseEnergyTradeoff
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:39.636843+00:00
-- url     : https://prove2.me/theorems/fc1eef38-ea85-4193-9e00-0879db9ac5ae
-- title:
--   Aether Catalog definitions — Novelty_SparseEnergyTradeoff
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SparseEnergyTradeoff`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SparseEnergyTradeoff.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_NeuralCoding

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

namespace NeuralCoding.SparseEnergyTradeoff

open Finset
open NeuralCoding

/-- All neural patterns whose spike-energy is at most `k`. -/
def budgetCodebook (N k : ℕ) : Finset (NeuralCode N) :=
  Finset.univ.filter (fun c => weight c ≤ k)

/-- All neural patterns using exactly `k` spikes. -/
def exactEnergyCodebook (N k : ℕ) : Finset (NeuralCode N) :=
  Finset.univ.filter (fun c => weight c = k)








end NeuralCoding.SparseEnergyTradeoff


