-- Prove2me | Theorems.Thm_PRNGSeed_lfsrRun_unitTap
-- name    : PRNGSeed.lfsrRun_unitTap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:47:28.29139+00:00
-- url     : https://prove2.me/theorems/3f0acf92-4d97-4786-8a75-fed47e264721
-- title:
--   The repeating register really repeats: its output at time `n` is the seed
-- statement:
--   The repeating register really repeats: its output at time `n` is the seed
--   symbol at index `n % p`.
--
--   ```lean
--   theorem PRNGSeed.lfsrRun_unitTap(p : ℕ) (hp : 0 < p) (init : Fin p → F) (n : ℕ) :
--       lfsrRun (unitTap p) init n = init ⟨n % p, Nat.mod_lt _ hp⟩ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PRNGSeedRecoveryLFSR.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PRNGSeedRecoveryLFSR.lean#L149

-- Thm stub generated from MachineLearning/PRNGSeedRecoveryLFSR.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Seed Recovery for Linear Feedback Shift Registers

This module formalises the mathematical core of *seed recovery* for the LFSR
family of pseudo-random generators, the first half of the "detect PRNG output
and replace the file by its seed" programme (see
`MachineLearning.PRNGCompressionBound` for the counting-side limits).

An LFSR of order `L` over a commutative ring `F` with tap vector
`c : Fin L → F` produces a stream `x : ℕ → F` obeying

  `x (n + L) = ∑ i < L, c i * x (n + i)`.

## Main results

* `lfsrRun` — the generator: run the register from an explicit seed.
* `lfsrRun_isLinRec`, `lfsrRun_of_lt` — the generator does what it claims.
* `IsLinRec.ext_of_agree` — **rigidity**: two streams with the same taps that
  agree on one window of length `L` agree forever.
* `IsLinRec.seed_recovery` — **the falsifiability gate**: any stream obeying the
  recurrence is *exactly* reproduced by re-running the register from its own
  first `L` symbols.  Nothing beyond the seed has to be stored.
* `linRec_taps_unique_of_span` — **Berlekamp–Massey uniqueness**: if the first
  `L` state windows span `F^L`, the tap vector is uniquely determined by the
  stream, so seed recovery has a unique answer.
* `hankel_span_of_taps_unique` — the converse over a field: tap uniqueness
  forces the windows to span.  Spanning is therefore *exactly* the right
  nondegeneracy condition.

## Application keywords

LFSR, linear recurrence, Berlekamp–Massey, seed recovery, PRNG fingerprinting,
stream compression
-/


open Finset

open PRNGSeed


variable {F : Type*} [CommRing F]



variable {L : ℕ} {c init : Fin L → F}








/-! ### Periodic data is seed-compressible -/

theorem PRNGSeed.lfsrRun_unitTap(p : ℕ) (hp : 0 < p) (init : Fin p → F) (n : ℕ) :
    lfsrRun (unitTap p) init n = init ⟨n % p, Nat.mod_lt _ hp⟩ := by sorry
