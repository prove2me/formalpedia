-- Prove2me | Theorems.Thm_YieldPostpone_Pricing_proposition_5
-- name    : YieldPostpone.Pricing.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:44.932013+00:00
-- url     : https://prove2.me/theorems/ad7ea384-62f4-436d-9e4b-c6201ad14f92
-- title:
--   Proposition 5, pp. 21–22 — pricing postponement: when it raises both profits and consumer surplus, and when it hurts the supplier
-- statement:
--   Compare ex ante pricing with responsive pricing (pricing postponement), under each payment scheme. Let $a, b > 0$, $\alpha, \theta \in (0,1)$, $\mu = \alpha(1-\theta)+\theta$, and consider costs $0 < c < a\mu/b$. Outcomes are the retailer's profit $\pi_R$, the supplier's profit $\pi_S$ and the expected consumer surplus $CS$ of subgame-perfect equilibria.
--
--   **(O) Pay-by-order (OA versus OR), any $\alpha \in (0,1)$.** For every such $c$ both scenarios have an equilibrium, and for any equilibrium of OA and any equilibrium of OR:
--   1. if $\max\{c^{OR}, c^{OA}_2, 0\} < c$, then $\pi^{OA}_R < \pi^{OR}_R$, $\pi^{OA}_S < \pi^{OR}_S$ and $CS^{OA} < CS^{OR}$;
--   2. the function $\Theta$ is strictly increasing on $(0,1)$, and if $\theta < \Theta(\alpha)$ then $c^{OA}_1 > \tilde C > 0$, and for $\tilde C < c < c^{OA}_1$ all three quantities increase from OA to OR as in 1;
--   3. if $c^{OR} > 0$, then for $0 < c < \min\{c^{OR}, c^{OA}_1\}$: $\pi^{OA}_R < \pi^{OR}_R$ and $CS^{OA} < CS^{OR}$, but $\pi^{OR}_S < \pi^{OA}_S$.
--
--   **(D) Pay-by-delivery (DA versus DR), $\alpha \ge 9/16$.** For every such $c$ both scenarios have an equilibrium, and for any equilibrium of DA and any equilibrium of DR:
--   1. if $c^{DR}_1 < c$, then $\pi^{DA}_R < \pi^{DR}_R$, $\pi^{DA}_S < \pi^{DR}_S$ and $CS^{DA} < CS^{DR}$;
--   2. if $c < c^{DR}_1$, then $\pi^{DA}_R = \pi^{DR}_R$, $\pi^{DA}_S = \pi^{DR}_S$ and $CS^{DA} = CS^{DR}$: the supply chain is unaffected.
--
--   Here
--   $$\Theta(\alpha) = \frac{\alpha\Big(3(1-\alpha-4\alpha^2) + 4\sqrt{\alpha(3+5\alpha+\alpha^2)}\Big)}{(1-\alpha)(3+4\alpha)^2},\qquad \tilde C = \frac{a\alpha\big(1-\sqrt{\alpha^2(1-\theta)+\theta}\big)}{b(1+\alpha)},$$
--   and $c^{OA}_1, c^{OA}_2, c^{OR}, c^{DR}_1$ are the thresholds of Appendix B (see the Setting).
--
--   Postponing the pricing decision until the yield is known is thus a Pareto improvement for the whole chain, consumers included, whenever production is costly enough, while at low cost under severe and likely yield loss it benefits the retailer and consumers at the supplier's expense.
--
--   **Formalization Note.** The paper's "there exists an increasing function $\Theta(\alpha)$" is instantiated with the explicit $\Theta$ of its proof (App. C, p. 39), and its monotonicity is part of the conclusion. $\tilde C$ is the explicit threshold (6), which App. C says is the one appearing in Proposition 5(O). Each comparison quantifies over all pairs of equilibria, and the existence clauses keep it from holding vacuously. Under the mission's equilibrium notion the consumer surplus of scenario DR between $c^{DR}_1$ and $c^{DR}_2$ differs from the value printed in Appendix B.4 (see Lemma 4); (D)(i) holds under both values. The interval of (D)(i) contains $c^{DR}_2$ and $c^{DA}$, where an equilibrium outcome is not unique; the inequalities are claimed there for every equilibrium, as printed.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), pp. 21–22, Proposition 5; App. C, proof of Proposition 5, PDF pp. 38–39 (appendix pp. 6–7), Θ(α); (6), PDF p. 37

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting

namespace YieldPostpone.Pricing

theorem proposition_5 (P : Params) (hP : P.Valid) :
    -- (O): pay-by-order, OA → OR, every α ∈ (0, 1)
    ((∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
        (∃ σ : Profile, IsSPE P c .OA σ) ∧ (∃ σ : Profile, IsSPE P c .OR σ)) ∧
     -- (O)(i)
     (∀ (c : ℝ) (σA σR : Profile), IsSPE P c .OA σA → IsSPE P c .OR σR →
        max (max (cOR P) (cOA2 P)) 0 < c → c < P.a * μ P / P.b →
          piR P .OA σA < piR P .OR σR ∧ piS P c .OA σA < piS P c .OR σR ∧
          CS P .OA σA < CS P .OR σR) ∧
     -- (O)(ii)
     (StrictMonoOn Theta (Set.Ioo 0 1) ∧
      (P.θ < Theta P.α →
        cOA1 P > Ctil P ∧ Ctil P > 0 ∧
        ∀ (c : ℝ) (σA σR : Profile), IsSPE P c .OA σA → IsSPE P c .OR σR →
          Ctil P < c → c < cOA1 P → c < P.a * μ P / P.b →
            piR P .OA σA < piR P .OR σR ∧ piS P c .OA σA < piS P c .OR σR ∧
            CS P .OA σA < CS P .OR σR)) ∧
     -- (O)(iii)
     (0 < cOR P →
        ∀ (c : ℝ) (σA σR : Profile), IsSPE P c .OA σA → IsSPE P c .OR σR →
          0 < c → c < min (cOR P) (cOA1 P) → c < P.a * μ P / P.b →
            piR P .OA σA < piR P .OR σR ∧ piS P c .OR σR < piS P c .OA σA ∧
            CS P .OA σA < CS P .OR σR)) ∧
    -- (D): pay-by-delivery, DA → DR, α ≥ 9/16
    (9 / 16 ≤ P.α →
      (∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
          (∃ σ : Profile, IsSPE P c .DA σ) ∧ (∃ σ : Profile, IsSPE P c .DR σ)) ∧
      ∀ (c : ℝ) (σA σR : Profile), IsSPE P c .DA σA → IsSPE P c .DR σR →
        0 < c → c < P.a * μ P / P.b →
          -- (D)(i)
          (cDR1 P < c →
            piR P .DA σA < piR P .DR σR ∧ piS P c .DA σA < piS P c .DR σR ∧
            CS P .DA σA < CS P .DR σR) ∧
          -- (D)(ii)
          (c < cDR1 P →
            piR P .DA σA = piR P .DR σR ∧ piS P c .DA σA = piS P c .DR σR ∧
            CS P .DA σA = CS P .DR σR)) := by sorry

end YieldPostpone.Pricing
