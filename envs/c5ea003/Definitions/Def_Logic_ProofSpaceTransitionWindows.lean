-- Prove2me | Definitions.Def_Logic_ProofSpaceTransitionWindows
-- name    : Logic_ProofSpaceTransitionWindows
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:02:36.20808+00:00
-- url     : https://prove2.me/theorems/023110dd-41b9-42db-9142-2c9fcd73eda2
-- title:
--   Aether Catalog definitions — Logic_ProofSpaceTransitionWindows
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ProofSpaceTransitionWindows`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ProofSpaceTransitionWindows.lean by skeleton subtraction
import Mathlib

/-!
# Transition Windows from Block Drift

A pointwise decrease assumption can be too rigid for cumulative proof-space
statistics.  This file replaces it by strict negative drift only at regularly
spaced block endpoints.  The resulting theorem produces a unique first sampled
crossing, proves permanence at all later sampled endpoints, and localizes the
unsampled crossing to one block of indices.
-/

namespace ProofSpaceTransitionWindows

/-- The signed excess in the exact shell at cutoff `n`. -/
def shellImbalance (provable unprovable : ℕ → ℕ) (n : ℕ) : ℤ :=
  (provable n : ℤ) - (unprovable n : ℤ)

/-- The cumulative signed excess through cutoff `n`. -/
def cumulativeImbalance (provable unprovable : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), shellImbalance provable unprovable i




/-- A sampled endpoint is the first nonpositive endpoint when all earlier
sampled endpoints are positive. -/
def IsFirstSampledThreshold (f : ℕ → ℤ) (block k : ℕ) : Prop :=
  f (k * block) ≤ 0 ∧ ∀ j < k, 0 < f (j * block)




end ProofSpaceTransitionWindows


