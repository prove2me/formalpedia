-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_linucb_expected_regret
-- name    : BanditAlgorithm.linear_bandit_linucb_expected_regret
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T16:39:32.381964+00:00
-- url     : https://prove2.me/theorems/39fdb25e-8fbd-4b2a-b427-8161fce34780
-- statement:
--   (Expected regret — Corollary 19.3) There is a universal constant $C > 0$ such that for every fixed finite action set $\mathrm{arms} : \mathrm{Fin}\,k \to \mathbb{R}^d$ with $\|\mathrm{arms}_j\|_2 \le L$ (with $L \ge 1$, $n \ge 2$) there is a policy $\pi$ (LinUCB with $\delta = 1/n$ and $\beta_t$ from Eq. (19.8)/Theorem 20.5) such that for every linear bandit instance with
--
--   - $\|\theta_*\|_2 \le 1$ (i.e. $m_2 = 1$ in Eq. (19.8)), and
--   - $\sup_{a,b}\langle\theta_*,a-b\rangle \le 1$ (= Assumption 19.1(b)),
--
--   the expected regret satisfies
--
--   $$R_n \le C d\sqrt{n}\log(nL).$$
-- source:
--   L&S Corollary 19.3, p.243

import Definitions.Def_StochasticLinearBandit
import Definitions.Def_banditRegret


open Matrix MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.linear_bandit_linucb_expected_regret :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d k n : ℕ) (L : ℝ), 0 < d → 0 < k → 2 ≤ n → 1 ≤ L →
        ∀ arms : Fin k → Fin d → ℝ,
          (∀ j, Real.sqrt (arms j ⬝ᵥ arms j) ≤ L) →
          ∃ π : BanditPolicy k,
            ∀ (θstar : Fin d → ℝ) (ν : StochasticBandit k),
              IsLinearBandit arms θstar ν →
              Real.sqrt (θstar ⬝ᵥ θstar) ≤ 1 →
              (∀ j j' : Fin k, θstar ⬝ᵥ (arms j - arms j') ≤ 1) →
              banditRegret ν π n ≤
                C * d * Real.sqrt n * Real.log (n * L) := by
  sorry
