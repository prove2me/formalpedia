-- Prove2me | Definitions.Def_asymptoticUcbPolicy
-- name    : asymptoticUcbPolicy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-19T02:56:46.243429+00:00
-- url     : https://prove2.me/theorems/16ac4d69-43ee-4859-b49c-7398548ed074
-- statement:
--   The asymptotically optimal UCB policy characterization (L&S Ch 8, Algorithm 6). It provides the confidence schedule
--
--   $$f(t) = 1 + t\log^2 t,$$
--
--   the index
--
--   $$\hat\mu_i(t-1) + \sqrt{\frac{2\log f(t)}{T_i(t-1)}}$$
--
--   computed in round $t = n+1$ from a history of $n$ completed rounds ($\infty$ when $T_i = 0$, encoded by the unpulled-arm clause), and the predicate `IsAsymptoticUCBPolicy` $\pi$, which holds iff each round $\pi$ deterministically plays an unpulled arm if one exists and otherwise an index maximizer (any tie-breaking).
-- source:
--   L&S Ch 8, Algorithm 6, p.117

import Definitions.Def_BanditPolicy

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapter 8, Algorithm 6,
p.117: the asymptotically optimal UCB policy.

The algorithm chooses each arm once and subsequently plays
`A_t = argmax_i (μ̂_i(t-1) + sqrt (2 log f(t) / T_i(t-1)))`, where
`f(t) = 1 + t log²(t)`. In the canonical model, a history of length `n`
determines the arm played in round `t = n + 1`, so the index computed from a
history of `n` completed rounds uses the confidence schedule `f (n + 1)`.
As for `IsUCBPolicy` (Algorithm 3), the index of an unpulled arm is `∞`,
encoded by the unpulled-arm clause; the policy predicate captures Algorithm 6
for every tie-breaking rule.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The confidence schedule `f(t) = 1 + t log²(t)` of L&S Algorithm 6. -/
noncomputable def asymptoticUcbSchedule (t : ℕ) : ℝ :=
  1 + t * Real.log t ^ 2

/-- The (finite part of the) index of arm `i` in round `t = n + 1` given a
history `h` of `n` completed rounds (L&S Algorithm 6):
`μ̂_i(t-1) + sqrt (2 log f(t) / T_i(t-1))` with `f(t) = 1 + t log²(t)`. -/
noncomputable def asymptoticUcbIndex {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) : ℝ :=
  armEmpiricalMean i h +
    Real.sqrt (2 * Real.log (asymptoticUcbSchedule (n + 1)) / armPullCount i h)

/-- `IsAsymptoticUCBPolicy π`: the policy `π` is an instance of the
asymptotically optimal UCB algorithm (L&S Algorithm 6, any tie-breaking):
each round it deterministically plays an unpulled arm if one exists
(index `∞`), and otherwise an arm maximizing the index
`μ̂_i(t-1) + sqrt (2 log f(t) / T_i(t-1))`, `f(t) = 1 + t log²(t)`. -/
def IsAsymptoticUCBPolicy {k : ℕ} (π : BanditPolicy k) : Prop :=
  ∀ n (h : BanditHistory k n), ∃ a : Fin k,
    (π.select n) h = Measure.dirac a ∧
    ((∃ j, armPullCount j h = 0) → armPullCount a h = 0) ∧
    ((∀ j, armPullCount j h ≠ 0) → ∀ j, asymptoticUcbIndex j h ≤ asymptoticUcbIndex a h)

end BanditAlgorithm


