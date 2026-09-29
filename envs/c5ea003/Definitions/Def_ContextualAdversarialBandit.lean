-- Prove2me | Definitions.Def_ContextualAdversarialBandit
-- name    : ContextualAdversarialBandit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-28T15:57:44.652377+00:00
-- url     : https://prove2.me/theorems/02d84e49-365f-4dff-938e-ec83977a25de
-- statement:
--   The adversarial contextual bandit / bandits with expert advice (L&S §18.2, Fig. 18.3): an adversary secretly fixes rewards $x_{ta} \in [0,1]$ and $M$ oblivious experts secretly fix advice matrices — in round $t$ expert $m$ recommends a probability distribution $E_t^{(m)}$ over the $k$ arms. The learner observes the advice, selects its own distribution, samples $A_t$ and observes only $X_t = x_{tA_t}$; the history and interconnection measure are exactly those of the plain adversarial bandit (`adversarialMeasure`, reused). The regret is against the best expert (Eq. (18.6)):
--
--   $$R_n = \max_{m} \sum_{t=1}^n \langle E_t^{(m)}, x_t\rangle - \mathbb{E}\Big[\sum_{t=1}^n X_t\Big],$$
--
--   the max outside the expectation since oblivious advice makes the benchmark deterministic.
-- source:
--   L&S Ch 18.2, pp.226-229

import Definitions.Def_AdversarialBandit

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), §18.2: bandits with
expert advice — the contextual adversarial bandit (Fig. 18.3).

The environment is the same `k`-armed adversarial bandit as in Ch 11: an
adversary secretly fixes a reward matrix `x` with `x t a ∈ [0,1]`. In
addition, `M` experts secretly fix their predictions: in round `t + 1`,
expert `m` recommends the probability vector `E t m ∈ 𝒫_{k-1}` over the
arms (a row of the advice matrix `E^{(t+1)} ∈ [0,1]^{M×k}`, Fig. 18.3; the
experts are oblivious — their advice does not depend on the learner's
actions). The learner observes the advice, selects its own distribution over
arms, samples `A_t` and observes only its own reward `X_t = x t A_t`.

Since the learner's observation in each round is exactly the pair
`(A_t, X_t)` (the advice sequence `E` is fixed data known in advance), the
history space, the policy object and the interconnection measure are
IDENTICAL to the plain adversarial bandit: a policy is a `BanditPolicy k`
and the distribution of the `n`-round history is `adversarialMeasure x π n`
(reused verbatim from `Def_AdversarialBandit`). What changes is only the
benchmark: the learner competes with the best EXPERT in hindsight rather
than the best fixed arm, Eq. (18.6):
`R_n = max_{m ∈ [M]} ∑_{t=1}^n ⟨E_t^{(m)}, x_t⟩ - E[∑_{t=1}^n X_t]`
(the benchmark is deterministic because the experts are oblivious, so the
`max` may be taken outside the expectation of Eq. (18.6)).

Simplex conditions on the rows of `E` (nonnegativity and summing to one) are
NOT baked into the data; they are stated as hypotheses of the theorems that
need them, exactly as `x t a ∈ [0,1]` is for the reward matrix.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The total reward collected by following expert `m`'s advice for the first
`n` rounds (L&S §18.2.1): `∑_{t=1}^n ⟨E_t^{(m)}, x_t⟩ = ∑_{t=1}^n ∑_{a ∈ [k]}
E_{t,m,a} x_{t,a}`, the expected reward of playing `A_t ~ E_t^{(m)}` in every
round. This is the quantity the benchmark expert `m*` of Eq. (18.8)
maximises. -/
noncomputable def expertTotalReward {k M : ℕ} (n : ℕ) (x : ℕ → Fin k → ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (m : Fin M) : ℝ :=
  ∑ t : Fin n, ∑ a, E t m a * x t a

/-- The expected regret of the policy `π` against the best of the `M` experts
`E` on the adversarial reward matrix `x` over horizon `n` (L&S Eq. (18.6)):
`R_n = max_{m ∈ [M]} ∑_{t=1}^n ⟨E_t^{(m)}, x_t⟩ - E[∑_{t=1}^n X_t]`,
the expectation taken over the interconnection measure `adversarialMeasure`
(which is unchanged from Ch 11: the advice is fixed data, so the learner's
history is still the sequence of (arm, reward) pairs). The benchmark `max` is
outside the expectation of Eq. (18.6) without loss because the experts are
oblivious, making `∑_t ⟨E_t^{(m)}, x_t⟩` deterministic. -/
noncomputable def exp4Regret {k M : ℕ} (n : ℕ) (x : ℕ → Fin k → ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (π : BanditPolicy k) : ℝ :=
  (⨆ m : Fin M, expertTotalReward n x E m) -
    ∫ h, (∑ t, (h t).2) ∂(adversarialMeasure x π n)

end BanditAlgorithm


