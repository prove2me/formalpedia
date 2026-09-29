-- Prove2me | Definitions.Def_MachineLearning_PRNGSeedRecoveryLCG
-- name    : MachineLearning_PRNGSeedRecoveryLCG
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:52:56.122395+00:00
-- url     : https://prove2.me/theorems/050146a2-b8fa-493f-9058-dc39564736b2
-- title:
--   Aether Catalog definitions — MachineLearning_PRNGSeedRecoveryLCG
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PRNGSeedRecoveryLCG`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PRNGSeedRecoveryLCG.lean by skeleton subtraction
import Mathlib
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

namespace PRNGSeed

section CommRing

variable {R : Type*} [CommRing R]

/-- One step of a linear congruential generator. -/
def lcgStep (a b : R) (x : R) : R := a * x + b

/-- The output stream of a linear congruential generator from seed `s`. -/
def lcgSeq (a b s : R) : ℕ → R
  | 0 => s
  | n + 1 => lcgStep a b (lcgSeq a b s n)







end CommRing

section Invertible

variable {R : Type*} [CommRing R] {a b : R}

/-- The inverse of one LCG step, for an invertible multiplier `a` with inverse `ai`. -/
def lcgUnstep (ai b : R) (y : R) : R := ai * (y - b)







variable [Fintype R]



end Invertible

section Counting

variable (m N : ℕ) [NeZero m]

/-- The set of length-`N` prefixes over `ℤ/m` that some LCG can produce. -/
noncomputable def lcgPrefixes : Finset (Fin N → ZMod m) :=
  (Finset.univ : Finset (ZMod m × ZMod m × ZMod m)).image
    fun t => fun i : Fin N => lcgSeq t.1 t.2.1 t.2.2 (i : ℕ)



end Counting

end PRNGSeed


