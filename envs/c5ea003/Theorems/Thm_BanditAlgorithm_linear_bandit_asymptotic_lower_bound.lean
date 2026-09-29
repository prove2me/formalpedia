-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_asymptotic_lower_bound
-- name    : BanditAlgorithm.linear_bandit_asymptotic_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T16:54:11.257184+00:00
-- url     : https://prove2.me/theorems/008ac006-2ec3-4c73-bcbb-318d9003210e
-- statement:
--   (Asymptotic instance-dependent lower bound, L&S Theorem 25.1 + Corollary 25.2) Let $\mathcal{A} = \{a_1,\dots,a_k\} \subset \mathbb{R}^d$ be finite and span $\mathbb{R}^d$, with unit-variance Gaussian rewards $X_t = \langle A_t,\theta\rangle + \eta_t$, and let $\pi$ be consistent on the class $\{\nu_{\theta'} : \theta' \in \mathbb{R}^d\}$ (Eq. (25.1): $R_n = o(n^p)$ for all $p>0$). Suppose $\theta$ has a unique optimal action, and write $\bar G_n = \mathbb{E}_\theta[\sum_{t=1}^n A_tA_t^\top]$. Then:
--
--   - (1) $\liminf_n \lambda_{\min}(\bar G_n)/\log n > 0$ (transcribed as a uniform quadratic-form bound $c\,\log n\,\|v\|^2 \le v^\top \bar G_n v$ eventually);
--   - (2) $\limsup_{n\to\infty} \log(n)\,\|a\|^2_{\bar G_n^{-1}} \le \Delta_a^2/2$ for every $a \in \mathcal{A}$;
--   - (3) $\liminf_{n\to\infty} R_n/\log n \ge c(\mathcal{A},\theta)$, where
--
--   $$c(\mathcal{A},\theta) = \inf_{\alpha \ge 0} \sum_a \alpha(a)\Delta_a \quad\text{subject to}\quad \|a\|^2_{H_\alpha^{-1}} \le \frac{\Delta_a^2}{2} \text{ for all suboptimal } a, \qquad H_\alpha = \sum_a \alpha(a)aa^\top$$
--
--   (allocations restricted to positive-definite $H_\alpha$).
-- source:
--   L&S Theorem 25.1 + Corollary 25.2, pp.296-297

import Definitions.Def_LinearBanditProtocol
import Definitions.Def_ConsistentBanditPolicy


open Matrix MeasureTheory ProbabilityTheory Filter ENNReal

theorem BanditAlgorithm.linear_bandit_asymptotic_lower_bound {k d : ℕ}
    (arms : Fin k → Fin d → ℝ) (hinj : Function.Injective arms)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤)
    (π : BanditPolicy k)
    (hcons : IsConsistentPolicy
      {ν : StochasticBandit k | ∃ θ' : Fin d → ℝ, ν = gaussianLinearBandit arms θ'} π)
    (θ : Fin d → ℝ) (jstar : Fin k)
    (hopt : ∀ j : Fin k, j ≠ jstar → arms j ⬝ᵥ θ < arms jstar ⬝ᵥ θ) :
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ v : Fin d → ℝ,
        c * Real.log n * (v ⬝ᵥ v) ≤
          v ⬝ᵥ linearBanditExpectedDesign arms (gaussianLinearBandit arms θ) π n *ᵥ v) ∧
    (∀ j : Fin k,
      atTop.limsup (fun n : ℕ ↦ ENNReal.ofReal (Real.log n *
          (arms j ⬝ᵥ
            (linearBanditExpectedDesign arms (gaussianLinearBandit arms θ) π n)⁻¹ *ᵥ
            arms j))) ≤
        ENNReal.ofReal (linearArmGap arms θ j ^ 2 / 2)) ∧
    ENNReal.ofReal (linearBanditAllocationValue arms θ) ≤
      atTop.liminf (fun n : ℕ ↦
        ENNReal.ofReal (banditRegret (gaussianLinearBandit arms θ) π n / Real.log n)) := by
  sorry
