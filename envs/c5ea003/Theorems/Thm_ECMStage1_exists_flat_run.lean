-- Prove2me | Theorems.Thm_ECMStage1_exists_flat_run
-- name    : ECMStage1.exists_flat_run
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:32:00.689682+00:00
-- url     : https://prove2.me/theorems/0563183b-d1e3-4823-b18e-2aa94df21605
-- title:
--   A long flat run.
-- statement:
--   **A long flat run.**  Some `Ï(B) / (Ï(m)+1)` of the schedule primes all carry the
--   same firing count: nothing whatsoever happens as the schedule advances through them.
--
--   ```lean
--   theorem ECMStage1.exists_flat_run{m B : ℕ} (hm : m ≠ 0) (hB : B ≠ 0) :
--       ∃ S ⊆ schedule B, primeCount B / (m.primeFactors.card + 1) ≤ S.card ∧
--         ∀ C ∈ S, ∀ C' ∈ S, Nat.gcd m (stage1 B C) = Nat.gcd m (stage1 B C') := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ECMStage1FlatRun.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ECMStage1FlatRun.lean#L61

-- Thm stub generated from Shared/ECMStage1FlatRun.lean
import Mathlib
import Definitions.Def_Shared_ECMStage1FlatRun
import Definitions.Def_Shared_ECMStage1OrderCompletion

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

open ECMStage1

open Finset

theorem ECMStage1.exists_flat_run{m B : ℕ} (hm : m ≠ 0) (hB : B ≠ 0) :
    ∃ S ⊆ schedule B, primeCount B / (m.primeFactors.card + 1) ≤ S.card ∧
      ∀ C ∈ S, ∀ C' ∈ S, Nat.gcd m (stage1 B C) = Nat.gcd m (stage1 B C') := by sorry
