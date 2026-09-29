-- Prove2me | Definitions.Def_etcPolicy
-- name    : etcPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-17T20:10:26.970296+00:00
-- url     : https://prove2.me/theorems/02b15038-e68a-4102-b93d-532506c8e17b
-- statement:
--   The Explore-Then-Commit policy characterization (L&S Algorithm 1): `IsETCPolicy hk m π` holds iff
--
--   - during the $mk$ exploration rounds, $\pi$ deterministically plays arm $t \bmod k$ at round $t$;
--   - afterwards, $\pi$ deterministically plays a committed maximizer of the exploration-prefix empirical means (any tie-breaking).
-- source:
--   L&S Ch 6, Algorithm 1, p.91

import Definitions.Def_BanditPolicy

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapter 6, Algorithm 1:
the Explore-Then-Commit policy with exploration parameter `m`.

ETC plays each of the `k` arms `m` times in round-robin order (rounds
`0, …, m k − 1`, 0-indexed), then commits: from round `m k` on it always plays
an arm maximizing the empirical mean computed from the exploration rounds.

We characterize ETC as a predicate on policies rather than constructing one
fixed kernel: `IsETCPolicy hk m π` holds iff `π` deterministically follows the
round-robin schedule during exploration and afterwards deterministically plays
a committed empirical-mean maximizer that depends only on the exploration
prefix. This captures Algorithm 1 for every tie-breaking rule.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The exploration prefix: the first `m * k` rounds of a history of length
`n ≥ m * k`. -/
def banditExplorationPrefix {k m n : ℕ} (hn : m * k ≤ n)
    (h : BanditHistory k n) : BanditHistory k (m * k) :=
  fun t ↦ h ⟨t, lt_of_lt_of_le t.2 hn⟩

/-- `IsETCPolicy hk m π`: the policy `π` is an instance of Explore-Then-Commit
with exploration parameter `m` (L&S Algorithm 1, any tie-breaking). -/
def IsETCPolicy {k : ℕ} (hk : 0 < k) (m : ℕ) (π : BanditPolicy k) : Prop :=
  ∃ commit : BanditHistory k (m * k) → Fin k,
    (∀ h₀ : BanditHistory k (m * k), ∀ j : Fin k,
        armEmpiricalMean j h₀ ≤ armEmpiricalMean (commit h₀) h₀) ∧
    (∀ n (h : BanditHistory k n),
        (∀ hlt : n < m * k, (π.select n) h = Measure.dirac ⟨n % k, Nat.mod_lt n hk⟩) ∧
        (∀ hge : m * k ≤ n,
          (π.select n) h = Measure.dirac (commit (banditExplorationPrefix hge h))))

end BanditAlgorithm


