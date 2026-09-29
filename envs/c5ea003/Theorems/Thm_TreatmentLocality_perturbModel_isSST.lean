-- Prove2me | Theorems.Thm_TreatmentLocality_perturbModel_isSST
-- name    : TreatmentLocality.perturbModel_isSST
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T03:48:44.396481+00:00
-- url     : https://prove2.me/theorems/d528a9b8-52a8-4349-a5f9-bf6701d75862
-- title:
--   The score perturbation stays inside the SST family
-- statement:
--   **The perturbation stays inside the SST family.** Let $M$ be an SST model of arXiv:2407.19618 with strictly positive transitions and Gaussian rewards, and let $(\alpha, \beta)$ be a direction whose transition part is centred,
--   $$\sum_j P(j \mid s, a)\,\beta(s,a,j) = 0 \quad\text{for every executed pair } (s,a).$$
--   Then there is $\varepsilon > 0$ such that for all $|t| < \varepsilon$ the perturbed model $M_t$ is again an SST model of the same family: it has the same crucial state, the same discount factor and the same reward variances, its rewards are Gaussian with means $m(s,a) + t\,\alpha(s,a)\sigma^2(s,a)$, its transitions are again strictly positive, and its transition weights are exactly the perturbed weights $P(j\mid s,a)(1 + t\beta(s,a,j))$.
--
--   This is the elementary but necessary first step of the Cramér-Rao argument: it says that the tangent direction really is tangent to a curve *inside* the model class over which unbiasedness is assumed. Centring is what makes the perturbed rows sum to one, positivity of the base transitions together with the finiteness of the state space is what keeps them non-negative for small $t$, and the variance profile is untouched because the family is parametrised by the reward means alone.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, Appendix EC.4 (the SST family parametrised by transition probabilities and reward means, at fixed crucial state, discount factor and reward variances, along which the constrained Cramér-Rao bound of Theorem 5 is computed).

import Definitions.Def_TreatmentLocalityPerturbation

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.perturbModel_isSST {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (m : S → Bool → ℝ) (v : S → Bool → ℝ≥0)
    (α : S → Bool → ℝ) (β : S → Bool → S → ℝ)
    (hcent : ∀ (s : S) (γ : Bool),
      ∑ j, (M.trans s (M.act γ s) j).toReal * β s (M.act γ s) j = 0)
    (hpos : ∀ s a j, 0 < M.trans s (M.act a s) j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      (perturbModel M m v α β t).crucial = M.crucial ∧
      (perturbModel M m v α β t).γdisc = M.γdisc ∧
      (perturbModel M m v α β t).GaussianRewards
        (fun s a => m s a + t * α s a * (v s a : ℝ)) v ∧
      (∀ s a j, 0 < (perturbModel M m v α β t).trans s
        ((perturbModel M m v α β t).act a s) j) ∧
      (∀ s a j, ((perturbModel M m v α β t).trans s a j).toReal
        = perturbCoef M β t s a j) := by sorry
