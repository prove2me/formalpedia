-- Prove2me | Theorems.Thm_PRNGSeed_exists_lcg_period
-- name    : PRNGSeed.exists_lcg_period
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:47:29.670608+00:00
-- url     : https://prove2.me/theorems/2cffb156-b23e-4a0a-97a0-5211d909b03b
-- title:
--   On a finite state space an invertible multiplier makes the orbit purely
-- statement:
--   On a finite state space an invertible multiplier makes the orbit purely
--   periodic: some positive `p` returns every state to itself.
--
--   ```lean
--   theorem PRNGSeed.exists_lcg_period{ai : R} (hai : ai * a = 1) :
--       ∃ p : ℕ, 0 < p ∧ ∀ x : R, (lcgStep a b)^[p] x = x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PRNGSeedRecoveryLCG.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PRNGSeedRecoveryLCG.lean#L150

-- Thm stub generated from MachineLearning/PRNGSeedRecoveryLCG.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLCG
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Seed Recovery for Linear Congruential Generators

Second family in the "detect PRNG output and store only the seed" programme
(compare `MachineLearning.PRNGSeedRecoveryLFSR` for shift registers and
`MachineLearning.PRNGCompressionBound` for the counting-side limits).

An LCG over a commutative ring `R` iterates `x ↦ a * x + b`.

## Main results

* `lcgSeq_isLinRec` — **fingerprinting bridge**: *every* LCG stream satisfies the
  order-`2` linear recurrence with taps `(-a, 1 + a)`.  So the Berlekamp–Massey
  machinery of the LFSR file already detects the whole LCG family, and no
  separate detector is needed.
* `lcgUnstep_iterate_seed` — **backward seed recovery**: with an invertible
  multiplier, the seed is recovered from the state at time `n` by `n` inverse
  steps, exactly.
* `lcgStep_bijective`, `exists_lcg_period`, `lcgSeq_add_period` — with an
  invertible multiplier on a finite ring the orbit is *purely* periodic.
* `lcg_seed_reachable_forward` — consequently the seed is recoverable by running
  the generator *forward* from any observed state: no inversion is needed.
* `lcg_prefix_card_le`, `exists_non_lcg_stream` — parameter counting: at most
  `m ^ 3` streams of any length are LCG streams over `ℤ/m`, so LCG-compressible
  data is vanishingly rare and a detector's false-positive budget is `m^{3-N}`.

## Application keywords

linear congruential generator, seed recovery, modular inversion, pure
periodicity, PRNG fingerprinting, compression
-/


open Finset

open PRNGSeed


variable {R : Type*} [CommRing R]











variable {R : Type*} [CommRing R] {a b : R}








variable [Fintype R]

theorem PRNGSeed.exists_lcg_period{ai : R} (hai : ai * a = 1) :
    ∃ p : ℕ, 0 < p ∧ ∀ x : R, (lcgStep a b)^[p] x = x := by sorry
