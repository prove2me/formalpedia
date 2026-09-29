-- Prove2me | Definitions.Def_exp4Policy
-- name    : exp4Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-28T15:58:02.610078+00:00
-- url     : https://prove2.me/theorems/b047247e-2df4-4a09-b839-275f5e7c8795
-- statement:
--   The Exp4 policy (L&S §18.3, Algorithm 11): maintain a distribution $Q_t$ over the $M$ experts starting from uniform $Q_1 = (1/M,\dots,1/M)$; in round $t$ play the mixture $P_t = Q_t E^{(t)}$, i.e. $P_{ta} = \sum_m Q_{tm} E^{(t)}_{ma}$, observe $X_t$, and form the importance-weighted arm estimates
--
--   $$\hat X_{ta} = 1 - \frac{\mathbb{1}\{A_t = a\}\,(1 - X_t)}{P_{ta} + \gamma};$$
--
--   propagate these to the experts via $\tilde X_{tm} = \langle E_t^{(m)}, \hat X_t\rangle$, and update $Q$ by exponential weighting:
--
--   $$Q_{t+1,m} \propto e^{\eta \tilde X_{tm}} Q_{tm} \qquad\text{(equivalently } Q_{t,m} \propto e^{\eta \tilde S_{t-1,m}} \text{ for the cumulative estimates).}$$
--
--   $\gamma$ enters only the estimator denominator. A policy IS Exp4 when every round's selection kernel equals this mixture distribution of the observed history.
-- source:
--   L&S Ch 18.3, Algorithm 11, p.229

import Definitions.Def_exp3Policy

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), §18.3, Algorithm 11
(Exp4: exponential weighting for exploration and exploitation with experts).

Exp4 with learning rate `η` and exploration parameter `γ` maintains a
probability distribution `Q_t` over the `M` experts, starting from the
uniform `Q_1 = (1/M, …, 1/M)` (line 2). In round `t` it plays the mixture of
the experts' advice `P_t = Q_t E^{(t)}`, i.e. `P_{t,a} = ∑_m Q_{t,m} E_{t,m,a}`
(line 5), samples `A_t ~ P_t`, observes `X_t = x_{t,A_t}` (line 6), forms the
loss-based importance-weighted arm estimates (line 7)
`X̂_{t,a} = 1 - 𝟙{A_t = a} (1 - X_t) / (P_{t,a} + γ)`,
propagates them to the experts (line 8) `X̃_{t,m} = ⟨E_t^{(m)}, X̂_t⟩`, and
updates `Q` by exponential weighting (line 9)
`Q_{t+1,m} = exp (η X̃_{t,m}) Q_{t,m} / ∑_j exp (η X̃_{t,j}) Q_{t,j}`.
Note `γ` enters ONLY the estimator's denominator (Exp3-IX-style implicit
exploration); the played distribution is the un-mixed `Q_t E^{(t)}`.
Theorem 18.1 analyses the original algorithm `γ = 0`.

Since `Q_1` is uniform, unrolling line 9 gives the closed form
`Q_{t,m} = exp (η S̃_{t-1,m}) / ∑_j exp (η S̃_{t-1,j})` where
`S̃_{t,m} = ∑_{s ≤ t} X̃_{s,m}` is the cumulative expert estimate — the same
`expWeights` shape as Exp3. As in `Def_exp3Policy`, `P_{t,a}` is itself a
function of the history before round `t`, so `S̃` is defined by recursion
over the history prefix: `exp4Estimate η γ E n h m` is `S̃_{n,m}` computed
from the `n` completed rounds recorded in `h`, `exp4ExpertWeights η γ E n h`
is `Q_{n+1}` and `exp4Prob η γ E n h` is the arm distribution `P_{n+1}`.

A policy (in the canonical sense of §4.6) *is* Exp4 when every round's
selection kernel is exactly this mixture distribution: `IsExp4Policy`.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The Exp4 cumulative expert-reward estimate `S̃_{n,m}` (L&S Algorithm 11,
lines 7–8) as a function of the `n` completed rounds: `S̃_{0,m} = 0` and
`S̃_{t,m} = S̃_{t-1,m} + ∑_a E_{t,m,a} X̂_{t,a}` with the importance-weighted
arm estimate `X̂_{t,a} = 1 - 𝟙{A_t = a} (1 - X_t) / (P_{t,a} + γ)`, where
`P_{t,a} = ∑_{m'} Q_{t,m'} E_{t,m',a}` is the mixture distribution played in
round `t` and `Q_{t,m'} = exp (η S̃_{t-1,m'}) / ∑_j exp (η S̃_{t-1,j})` is
the exponential-weights expert distribution computed from the first `t - 1`
rounds. -/
noncomputable def exp4Estimate {k M : ℕ} (η γ : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) :
    (n : ℕ) → BanditHistory k n → Fin M → ℝ
  | 0, _, _ => 0
  | n + 1, h, m =>
      exp4Estimate η γ E n (Fin.init h) m +
        ∑ a, E n m a *
          (1 - if (h (Fin.last n)).1 = a then
              (1 - (h (Fin.last n)).2) /
                ((∑ m', expWeights
                      (fun j ↦ η * exp4Estimate η γ E n (Fin.init h) j) m' *
                    E n m' a) + γ)
            else 0)

/-- The Exp4 expert distribution `Q_{n+1}` for the round following the `n`
recorded rounds of `h` (L&S Algorithm 11, lines 2 and 9, in unrolled
exponential-weights form): `Q_{n+1,m} = exp (η S̃_{n,m}) / ∑_j exp (η S̃_{n,j})`. -/
noncomputable def exp4ExpertWeights {k M : ℕ} (η γ : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (n : ℕ) (h : BanditHistory k n)
    (m : Fin M) : ℝ :=
  expWeights (fun j ↦ η * exp4Estimate η γ E n h j) m

/-- The Exp4 arm-sampling distribution `P_{n+1}` for the round following the
`n` recorded rounds of `h` (L&S Algorithm 11, line 5): the mixture of the
experts' advice under the current expert distribution,
`P_{n+1,a} = (Q_{n+1} E^{(n+1)})_a = ∑_m Q_{n+1,m} E_{n+1,m,a}`. -/
noncomputable def exp4Prob {k M : ℕ} (η γ : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (n : ℕ) (h : BanditHistory k n)
    (a : Fin k) : ℝ :=
  ∑ m, exp4ExpertWeights η γ E n h m * E n m a

/-- With no data the expert distribution is uniform: `Q_{1,m} = 1/M`
(L&S Algorithm 11, line 2). -/
lemma exp4ExpertWeights_zero {k M : ℕ} (η γ : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (h : BanditHistory k 0) (m : Fin M) :
    exp4ExpertWeights η γ E 0 h m = 1 / M := by
  simp [exp4ExpertWeights, expWeights, exp4Estimate]

/-- With no data, Exp4 plays the uniform mixture of the round-one advice:
`P_{1,a} = (1/M) ∑_m E_{1,m,a}`. -/
lemma exp4Prob_zero {k M : ℕ} (η γ : ℝ) (E : ℕ → Fin M → Fin k → ℝ)
    (h : BanditHistory k 0) (a : Fin k) :
    exp4Prob η γ E 0 h a = (∑ m, E 0 m a) / M := by
  simp only [exp4Prob, exp4ExpertWeights_zero, Finset.sum_div]
  exact Finset.sum_congr rfl fun m _ ↦ one_div_mul_eq_div _ _

/-- `IsExp4Policy η γ E π`: the policy `π` is Exp4 with learning rate `η`,
exploration parameter `γ` and expert advice `E` (L&S Algorithm 11): in every
round the selection kernel is exactly the mixture-of-experts distribution
`exp4Prob η γ E` of the observed history. -/
def IsExp4Policy {k M : ℕ} (η γ : ℝ) (E : ℕ → Fin M → Fin k → ℝ)
    (π : BanditPolicy k) : Prop :=
  ∀ (n : ℕ) (h : BanditHistory k n),
    (π.select n) h = ∑ a, ENNReal.ofReal (exp4Prob η γ E n h a) • Measure.dirac a

end BanditAlgorithm


