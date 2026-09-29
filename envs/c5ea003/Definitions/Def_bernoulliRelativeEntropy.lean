-- Prove2me | Definitions.Def_bernoulliRelativeEntropy
-- name    : bernoulliRelativeEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-26T01:49:29.743362+00:00
-- url     : https://prove2.me/theorems/c377b8fc-42f9-4c49-bc63-4a26f07f3614
-- statement:
--   The relative entropy between Bernoulli distributions with parameters $p, q$ (L&S Definition 10.1):
--
--   $$d(p,q) = p\log\frac{p}{q} + (1-p)\log\frac{1-p}{1-q},$$
--
--   real-valued via Lean's junk conventions $x/0 = 0$, $\log 0 = 0$ (agrees with the book's limit conventions for all $p \in [0,1]$ whenever $q \in (0,1)$; at $q \in \{0,1\}$, $p \ne q$ the book's value is $\infty$ and the formula returns a finite junk value, so theorems carry $q \in (0,1)$-type hypotheses where needed). The file also provides the Bernoulli bandit environment `bernoulliBandit` (arm $i$ has reward law $\mu_i\delta_1 + (1-\mu_i)\delta_0$), the exploration function $f(t) = 1 + t\log^2 t$, the KL-UCB index
--
--   $$\max\left\{\mu' \in [0,1] : d(\hat\mu_i(t-1), \mu') \le \frac{\log f(t)}{T_i(t-1)}\right\}$$
--
--   (with the book's singular conventions $d(p,0)=d(p,1)=\infty$ for $p\ne 0$, resp. $p \ne 1$, encoded as explicit guards in the constraint set), and the predicate `IsKLUCBPolicy` for Algorithm 8 (choose each arm once, then play an index-maximizing arm; deterministic argmax, any tie-breaking), mirroring `IsUCBPolicy`.
-- source:
--   L&S Definition 10.1, p.134

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_BanditPolicy

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapter 10:
Bernoulli bandits and the KL-UCB algorithm.

* `bernoulliRelativeEntropy p q` — Definition 10.1: the relative entropy
  `d(p, q) = p log(p/q) + (1-p) log((1-p)/(1-q))` between Bernoulli
  distributions with parameters `p, q`.

  **Junk-value convention.** The book extends `d` by limits:
  `d(0,q) = log(1/(1-q))`, `d(1,q) = log(1/q)`, and `d(p,q) = ∞` for
  `q ∈ {0,1}`, `p ≠ q`. We keep `d` real-valued and rely on Lean's
  conventions `x/0 = 0` and `log 0 = 0`. Consequences:
  - for `q ∈ (0,1)` and any `p ∈ [0,1]` (including `p ∈ {0,1}`) the formula
    agrees exactly with the book's limits;
  - at `q ∈ {0,1}` with `p ≠ q` the value is a finite junk value (where the
    book has `∞`), so theorems needing those cases carry `q ∈ (0,1)`-type
    hypotheses, and the KL-UCB index set below encodes the book's
    `d(p,0) = d(p,1) = ∞` (`p ≠ 0`, resp. `p ≠ 1`) conventions explicitly.

* `bernoulliBandit μvec hμ` — the Bernoulli bandit with mean vector
  `μvec ∈ [0,1]^k`: arm `i` has the two-point reward distribution
  `μvec i • δ_1 + (1 - μvec i) • δ_0` (Ch 10, p.133).

* `klucbExploration`, `klucbIndex`, `IsKLUCBPolicy` — Algorithm 8 (p.137):
  choose each arm once, then play
  `A_t = argmax_i max { μ' ∈ [0,1] : d(μ̂_i(t-1), μ') ≤ log f(t) / T_i(t-1) }`
  with `f(t) = 1 + t log² t`. As in `IsUCBPolicy`, the policy is characterized
  by deterministic-argmax clauses, covering every tie-breaking rule.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The relative entropy between Bernoulli distributions with parameters
`p` and `q` (L&S Definition 10.1):
`d(p, q) = p log(p/q) + (1-p) log((1-p)/(1-q))`.

Real-valued, using Lean's junk conventions `x/0 = 0`, `log 0 = 0`; this matches
the book's limit conventions whenever `q ∈ (0,1)`, while at `q ∈ {0,1}`,
`p ≠ q` the book's value is `∞` and this formula returns a junk real. -/
noncomputable def bernoulliRelativeEntropy (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- The Bernoulli bandit with mean vector `μvec ∈ [0,1]^k` (L&S Ch 10, p.133):
arm `i` yields reward `1` with probability `μvec i` and reward `0` otherwise,
i.e. its reward distribution is the two-point measure
`μvec i • δ_1 + (1 - μvec i) • δ_0`. -/
noncomputable def bernoulliBandit {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) : StochasticBandit k where
  P i := ENNReal.ofReal (μvec i) • Measure.dirac (1 : ℝ) +
      ENNReal.ofReal (1 - μvec i) • Measure.dirac (0 : ℝ)
  prob i := by
    constructor
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ← ENNReal.ofReal_add (hμ i).1 (by linarith [(hμ i).2])]
    norm_num

/-- The KL-UCB exploration function `f(t) = 1 + t log² t` (L&S Algorithm 8). -/
noncomputable def klucbExploration (t : ℕ) : ℝ :=
  1 + t * Real.log t ^ 2

/-- The KL-UCB index of arm `i` after the `n` completed rounds recorded in `h`
(i.e. the index used to select the arm of round `t = n + 1`), L&S Algorithm 8:

`max { μ' ∈ [0,1] : d(μ̂_i(t-1), μ') ≤ log f(t) / T_i(t-1) }`.

The book's singular conventions `d(p, 0) = ∞` for `p ≠ 0` and `d(p, 1) = ∞`
for `p ≠ 1` (which the real-valued `bernoulliRelativeEntropy` cannot express)
are encoded by the explicit guards `μ' = 0 → μ̂_i = 0` and `μ' = 1 → μ̂_i = 1`,
so the set below is *exactly* the book's constraint set. -/
noncomputable def klucbIndex {k n : ℕ} (i : Fin k) (h : BanditHistory k n) : ℝ :=
  sSup {μ' ∈ Set.Icc (0 : ℝ) 1 |
    bernoulliRelativeEntropy (armEmpiricalMean i h) μ' ≤
        Real.log (klucbExploration (n + 1)) / armPullCount i h ∧
      (μ' = 0 → armEmpiricalMean i h = 0) ∧
      (μ' = 1 → armEmpiricalMean i h = 1)}

/-- `IsKLUCBPolicy π`: the policy `π` is an instance of KL-UCB
(L&S Algorithm 8, any tie-breaking): each round it deterministically plays an
unpulled arm if one exists (the initialization "choose each arm once"), and
otherwise an arm maximizing the KL-UCB index. -/
def IsKLUCBPolicy {k : ℕ} (π : BanditPolicy k) : Prop :=
  ∀ n (h : BanditHistory k n), ∃ a : Fin k,
    (π.select n) h = Measure.dirac a ∧
    ((∃ j, armPullCount j h = 0) → armPullCount a h = 0) ∧
    ((∀ j, armPullCount j h ≠ 0) → ∀ j, klucbIndex j h ≤ klucbIndex a h)

end BanditAlgorithm


