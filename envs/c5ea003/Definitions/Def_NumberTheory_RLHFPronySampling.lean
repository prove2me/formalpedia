-- Prove2me | Definitions.Def_NumberTheory_RLHFPronySampling
-- name    : NumberTheory_RLHFPronySampling
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:58.393615+00:00
-- url     : https://prove2.me/theorems/f60ce0ae-6908-46fd-b387-1dba52982847
-- title:
--   Aether Catalog definitions — NumberTheory_RLHFPronySampling
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.RLHFPronySampling`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/RLHFPronySampling.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_RLHFSpectralRigidity

/-!
# Finite-sample spectral rigidity: how many temperatures does a reward audit need?

`RLHF.spectral_rigidity` recovers the reward spectrum of an RLHF problem from the value of
the partition function at *every* positive temperature.  This file makes the statement
finite, in both directions, settling the two-atom case of the "Prony count" conjecture
recorded in `FUTURE_DIRECTIONS.md`.

* `RLHF.exp_sample_uniqueness` — **known levels, `n` samples suffice.**  If the candidate
  reward levels `v₀, …, v_{n-1}` are known and distinct, then the masses carried by them are
  determined by the partition function at the `n` arithmetically spaced inverse temperatures
  `t₀, t₀ + τ, …, t₀ + (n−1)τ`.  The engine is a *generalized Vandermonde* determinant: on an
  arithmetic grid of temperatures the exponential-sum system becomes an honest Vandermonde
  system in the variables `e^{v_j τ}`, which are distinct because `exp` is injective.
* `RLHF.spectral_rigidity_sampled` — the RLHF form of the same statement: two RLHF problems
  whose reward values lie in a common known finite list and whose partition functions agree
  at `n` equally spaced inverse temperatures have identical reward spectra.
* `RLHF.prony_three_samples_insufficient` — **unknown levels: three temperatures are not
  enough.**  Two explicit two-atom RLHF problems on `Bool`, with pairwise distinct reward
  levels, whose partition functions agree at the three inverse temperatures `t = 0, 1, 2`,
  and whose reward spectra differ.  The construction is a moment coincidence: the two-point
  distributions `{1, 3}` with masses `(1/2, 1/2)` and `{3/2, 4}` with masses `(4/5, 1/5)`
  have the same mean `2` and the same second moment `5`, and taking logarithms of the
  support turns those two moment equations into agreement of the partition functions at
  `t = 1` and `t = 2` (agreement at `t = 0` being normalization).

Together: the sampling count is governed by whether the reward *levels* are known.  With
known levels `n` measurements are enough; with unknown levels, `2n − 1 = 3` measurements are
provably not enough for `n = 2` atoms.
-/

namespace RLHF

open Finset

/-! ## 1. Known levels: an arithmetic grid of `n` temperatures suffices -/



/-! ## 2. Unknown levels: three temperatures are not enough -/

/-- The partition function of a two-atom reward spectrum: mass `w` at level `u` and mass
`1 − w` at level `v`, read at inverse temperature `t`. -/
noncomputable def twoAtomZ (w u v t : ℝ) : ℝ :=
  w * Real.exp (u * t) + (1 - w) * Real.exp (v * t)







end RLHF


