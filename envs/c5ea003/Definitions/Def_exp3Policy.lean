-- Prove2me | Definitions.Def_exp3Policy
-- name    : exp3Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-17T23:27:14.124834+00:00
-- url     : https://prove2.me/theorems/56d199a2-f371-42c6-a7f4-9e2e15dada4f
-- statement:
--   The Exp3 policy (Algorithm 9) with learning rate $\eta$: the sampling distribution and loss-based importance-weighted reward estimator are (Eq. 11.6/11.7)
--
--   $$P_{ti} \propto \exp(\eta \hat S_{t-1,i}), \qquad \hat S_{ti} = \sum_{s\le t} \hat X_{si}, \qquad \hat X_{ti} = 1 - \frac{\mathbb{1}\{A_t=i\}(1-X_t)}{P_{ti}};$$
--
--   the cumulative estimate `exp3Estimate` is defined by recursion over the history prefix and `IsExp3Policy` states the selection kernel has pmf `exp3Prob`. Also the Exp3-IX policy (Algorithm 10) with parameters $\eta, \gamma$ (Eq. 12.4):
--
--   $$P_{ti} \propto \exp(-\eta \hat L_{t-1,i}) \quad\text{with biased loss estimator}\quad \hat Y_{ti} = \frac{\mathbb{1}\{A_t=i\}(1-X_t)}{P_{ti}+\gamma},$$
--
--   as `exp3IXEstimate`/`exp3IXProb`/`IsExp3IXPolicy`.
-- source:
--   L&S Ch 11.2-11.3, Algorithm 9, pp.150-153

import Definitions.Def_BanditPolicy
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), §11.3, Algorithm 9
(Exp3) and §12.1, Algorithm 10 (Exp3-IX).

Exp3 with learning rate `η` maintains cumulative reward estimates
`Ŝ_{t,i} = ∑_{s ≤ t} X̂_{s,i}` built from the loss-based importance-weighted
estimator (Eq. (11.6))
`X̂_{t,i} = 1 - 𝟙{A_t = i} (1 - X_t) / P_{t,i}`,
and samples round `t + 1`'s arm from the exponential-weights distribution
(Eq. (11.7)) `P_{t+1,i} = exp (η Ŝ_{t,i}) / ∑_j exp (η Ŝ_{t,j})`.

Since `P_{t,i}` is itself a function of the history before round `t`, the
estimates are defined by recursion over the history prefix: `exp3Estimate η n h`
is `Ŝ_n` computed from the `n` completed rounds recorded in `h`, and
`exp3Prob η n h` is the sampling distribution for round `n + 1`. In round `0`
(no data) the distribution is uniform: `exp3Prob η 0 h i = 1 / k`.

Exp3-IX (Algorithm 10) works with cumulative loss estimates
`L̂_{t,i} = ∑_{s ≤ t} Ŷ_{s,i}` built from the biased estimator (Eq. (12.4))
`Ŷ_{t,i} = 𝟙{A_t = i} (1 - X_t) / (P_{t,i} + γ)`,
and samples from `P_{t+1,i} = exp (-η L̂_{t,i}) / ∑_j exp (-η L̂_{t,j})`.

A policy (in the canonical sense of §4.6) *is* Exp3 / Exp3-IX when every
round's selection kernel is exactly the corresponding exponential-weights
distribution; this is the predicate `IsExp3Policy` / `IsExp3IXPolicy`.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The exponential-weights probability vector of a score vector `s`:
`expWeights s i = exp (s i) / ∑ j exp (s j)`. -/
noncomputable def expWeights {k : ℕ} (s : Fin k → ℝ) (i : Fin k) : ℝ :=
  Real.exp (s i) / ∑ j, Real.exp (s j)

/-- The Exp3 cumulative reward estimate `Ŝ_{n,i}` (L&S Algorithm 9, line 6)
as a function of the `n` completed rounds: `Ŝ_{0,i} = 0` and
`Ŝ_{t,i} = Ŝ_{t-1,i} + 1 - 𝟙{A_t = i} (1 - X_t) / P_{t,i}`, where `P_{t,i}`
is the exponential-weights probability computed from the first `t - 1`
rounds (Eq. (11.6), the loss-based importance-weighted estimator). -/
noncomputable def exp3Estimate {k : ℕ} (η : ℝ) :
    (n : ℕ) → BanditHistory k n → Fin k → ℝ
  | 0, _, _ => 0
  | n + 1, h, i =>
      exp3Estimate η n (Fin.init h) i +
        (1 - if (h (Fin.last n)).1 = i then
            (1 - (h (Fin.last n)).2) /
              expWeights (fun j ↦ η * exp3Estimate η n (Fin.init h) j) i
          else 0)

/-- The Exp3 sampling distribution for the round following the `n` recorded
rounds of `h` (L&S Eq. (11.7)):
`P_{n+1,i} = exp (η Ŝ_{n,i}) / ∑_j exp (η Ŝ_{n,j})`. -/
noncomputable def exp3Prob {k : ℕ} (η : ℝ) (n : ℕ) (h : BanditHistory k n)
    (i : Fin k) : ℝ :=
  expWeights (fun j ↦ η * exp3Estimate η n h j) i

/-- With no data, Exp3 samples uniformly: `P_{1,i} = 1/k`. -/
lemma exp3Prob_zero {k : ℕ} (η : ℝ) (h : BanditHistory k 0) (i : Fin k) :
    exp3Prob η 0 h i = 1 / k := by
  simp [exp3Prob, expWeights, exp3Estimate]

/-- `IsExp3Policy η π`: the policy `π` is Exp3 with learning rate `η`
(L&S Algorithm 9): in every round the selection kernel is exactly the
exponential-weights distribution `exp3Prob η` of the observed history. -/
def IsExp3Policy {k : ℕ} (η : ℝ) (π : BanditPolicy k) : Prop :=
  ∀ (n : ℕ) (h : BanditHistory k n),
    (π.select n) h = ∑ i, ENNReal.ofReal (exp3Prob η n h i) • Measure.dirac i

/-- The Exp3-IX cumulative loss estimate `L̂_{n,i}` (L&S Algorithm 10,
line 6) as a function of the `n` completed rounds: `L̂_{0,i} = 0` and
`L̂_{t,i} = L̂_{t-1,i} + 𝟙{A_t = i} (1 - X_t) / (P_{t,i} + γ)`, where
`P_{t,i}` is the exponential-weights probability of the negated scaled
losses computed from the first `t - 1` rounds (Eq. (12.4), the biased
loss estimator with implicit-exploration parameter `γ`). -/
noncomputable def exp3IXEstimate {k : ℕ} (η γ : ℝ) :
    (n : ℕ) → BanditHistory k n → Fin k → ℝ
  | 0, _, _ => 0
  | n + 1, h, i =>
      exp3IXEstimate η γ n (Fin.init h) i +
        (if (h (Fin.last n)).1 = i then
          (1 - (h (Fin.last n)).2) /
            (expWeights (fun j ↦ -(η * exp3IXEstimate η γ n (Fin.init h) j)) i
              + γ)
        else 0)

/-- The Exp3-IX sampling distribution for the round following the `n`
recorded rounds of `h` (L&S Algorithm 10, line 4):
`P_{n+1,i} = exp (-η L̂_{n,i}) / ∑_j exp (-η L̂_{n,j})`. -/
noncomputable def exp3IXProb {k : ℕ} (η γ : ℝ) (n : ℕ)
    (h : BanditHistory k n) (i : Fin k) : ℝ :=
  expWeights (fun j ↦ -(η * exp3IXEstimate η γ n h j)) i

/-- `IsExp3IXPolicy η γ π`: the policy `π` is Exp3-IX with learning rate `η`
and implicit-exploration parameter `γ` (L&S Algorithm 10): in every round the
selection kernel is exactly the exponential-weights distribution
`exp3IXProb η γ` of the observed history. -/
def IsExp3IXPolicy {k : ℕ} (η γ : ℝ) (π : BanditPolicy k) : Prop :=
  ∀ (n : ℕ) (h : BanditHistory k n),
    (π.select n) h =
      ∑ i, ENNReal.ofReal (exp3IXProb η γ n h i) • Measure.dirac i

end BanditAlgorithm


