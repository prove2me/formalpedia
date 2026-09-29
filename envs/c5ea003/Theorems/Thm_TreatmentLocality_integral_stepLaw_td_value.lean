-- Prove2me | Theorems.Thm_TreatmentLocality_integral_stepLaw_td_value
-- name    : TreatmentLocality.integral_stepLaw_td_value
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:54:31.854474+00:00
-- url     : https://prove2.me/theorems/846faad0-cb2c-42f2-9562-2afcd633e7c7
-- title:
--   The weighted temporal-difference error of the true value function is centred
-- statement:
--   **The inverse-probability-weighted temporal-difference error of the true value function is centred.** Fix a state $s$ of the SST model and an arm $a$, and let the experiment take one step from $s$ under the mixed policy $\pi^{1/2}$: a fair coin picks an arm $\gamma$, the executed action is $\mathrm{act}(\gamma, s)$, and $(s', r)$ are drawn from the corresponding transition and reward laws. Weight the observation by the information-sharing weight $w_a = 2\cdot\mathbf 1[\gamma = a]$ at the crucial state and $w_a = 1$ elsewhere. Then
--   $$\mathbb{E}\Bigl[w_a \bigl(r + \gamma_{\mathrm{disc}} V^a(s') - V^a(s)\bigr)\Bigr] \;=\; 0 .$$
--
--   Two mechanisms meet here. First, the weight makes the expectation an arm-$a$ expectation: at the crucial state the factor $2\cdot\mathbf 1[\gamma=a]$ cancels the fair coin exactly, and away from the crucial state both arms execute the same action, so the unweighted shared sample already reports the arm-$a$ law. What is left is $r^a(s) + \gamma (P^a V^a)(s) - V^a(s)$. Second, that quantity vanishes by the Bellman equation. This is the centring that makes the influence function of the information-sharing estimator a martingale difference (arXiv:2407.19618, §6.2).
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3: Remark 1 and Proposition 5 (the model-based plug-in estimator), §6.2 (the information-sharing statistics), and Appendix EC.3.2 (the linearisation of a differentiable estimator and its asymptotic covariance, Lemma EC.4-EC.5).

import Definitions.Def_TreatmentLocalityPlugIn
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.integral_stepLaw_td_value {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S) (s : S) (a : Bool)
    (hR : ∀ x y, Integrable (fun r : ℝ => r) (M.reward x y)) :
    ∫ p : Bool × S × ℝ,
        ((if s = M.crucial then 2 * (if p.1 = a then (1 : ℝ) else 0) else 1)
          * (p.2.2 + M.γdisc * M.value a p.2.1 - M.value a s)) ∂(stepLaw M s)
      = 0 := by sorry
