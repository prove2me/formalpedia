-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesian_ts_terminal_conditional_laws
-- name    : BanditAlgorithm.bayesian_ts_terminal_conditional_laws
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T04:31:02.667795+00:00
-- url     : https://prove2.me/theorems/90774e54-89a6-492c-95ab-192834c793e5
-- title:
--   Conditional laws of a Bayesian bandit round
-- statement:
--   In the Bayesian adversarial bandit model, fix a round $t$ and condition on the history $H_t$ strictly before that round. Let $R_h$ denote the posterior law of the full reward matrix and let $\pi_t(h)$ denote the policy’s action law. Then, for almost every history $h$:
--
--   $$
--   \mathcal L(X\mid H_t=h)=R_h,
--   \qquad
--   \mathcal L(X,A_t\mid H_t=h)=R_h\otimes\pi_t(h).
--   $$
--
--   Moreover, under the terminal generative law, the recorded observation is consistent with the reward matrix:
--
--   $$
--   (A_t,Y_t)=(A_t,X_{t,A_t})\quad\text{almost surely}.
--   $$
--
--   These identities are a formal bridge from the recursively generated bandit history to the posterior product law used in the one-round Thompson-sampling information argument.
--
--   **Formalization Note** The posterior $R_h$ is the regular conditional distribution of the reward matrix under the prefix measure at time $t$.
-- source:
--   Purely formal bridge from the generative definitions in Def_ThompsonSampling to Lattimore and Szepesvari, Bandit Algorithms (2020), Lemma 36.7, printed p. 470 / free PDF p. 479.

import Definitions.Def_BayesianTSRoundConditionalGains
import Theorems.Thm_BanditAlgorithm_bayesianAdversarialMeasure_prefix_marginal
import Mathlib.Probability.Kernel.CompProdEqIff

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

theorem bayesian_ts_terminal_conditional_laws
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : Fin n) :
    let terminal := bayesianAdversarialMeasure Q pi n le_rfl
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let base := bayesianAdversarialMeasure Q pi t.1 (Nat.le_of_lt t.2)
    let nu := Measure.map history terminal
    let post := condDistrib Prod.fst Prod.snd base
    (condDistrib Prod.fst history terminal =ᵐ[nu] post) ∧
    (condDistrib (fun p ↦ (p.1, (p.2 t).1)) history terminal =ᵐ[nu]
      post.prod (pi.select t.1)) ∧
    (∀ᵐ z ∂terminal, z.2 t = ((z.2 t).1, z.1 t (z.2 t).1)) := by sorry
