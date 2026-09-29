-- Prove2me | Definitions.Def_Shared_ECMStage1FlatRun
-- name    : Shared_ECMStage1FlatRun
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:44.437893+00:00
-- url     : https://prove2.me/theorems/62b155ce-755c-4a04-af8f-814581f2c151
-- title:
--   Aether Catalog definitions — Shared_ECMStage1FlatRun
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.ECMStage1FlatRun`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/ECMStage1FlatRun.lean by skeleton subtraction
import Mathlib

/-!
# A long flat run in the schedule: the pigeonhole behind the observed non-uniformity

The staircase results of `Catalog.Shared.ECMStage1FiringRate` say that the cumulative
firing count `C ↦ gcd(m, k(B,C))` jumps exactly at the prime divisors of the order below
the bound, hence at most `ω(m)` times.  Here we draw the consequence that the
experimental KS analysis was really detecting: since the schedule has `π(B)` steps and
the staircase has at most `ω(m)` jumps, **some block of the schedule of length at least
`π(B) / (ω(m)+1)` does nothing at all**.

* `firing_count_eq_of_same_jump_count` — two schedule primes with the same number of
  jumps below them carry the same firing count.
* `exists_flat_run` — a set of at least `π(B) / (ω(m)+1)` schedule primes on which the
  firing count is constant.
* `exists_flat_run_half` — the readable corollary: for an order with at most one prime
  divisor below the bound, at least half the schedule is inert.

The uniform comparison distribution increases at every one of the `π(B)` steps, so a flat
run of that length is exactly the obstruction to uniformity that the KS statistic picks
up; the quantitative sup-distance version is conjecture 1 of `FUTURE_DIRECTIONS.md`.
-/

namespace ECMStage1

open Finset

/-- The schedule: the primes at most `B`, in the order stage 1 visits them. -/
def schedule (B : ℕ) : Finset ℕ := (Finset.range (B + 1)).filter Nat.Prime





end ECMStage1


