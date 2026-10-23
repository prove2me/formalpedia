-- Prove2me | Theorems.Thm_YieldPostpone_Preference_proposition_2
-- name    : YieldPostpone.Preference.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:26.034143+00:00
-- url     : https://prove2.me/theorems/ac1eb51e-d51a-4231-a53c-571766142314
-- title:
--   Proposition 2, p. 16 — for α ≥ 9/16 the retailer's equilibrium profit ranks DA, OR, DR, OR first as c crosses C̃, c^DR_1, c^DR_2
-- statement:
--   Let $a,b>0$, $\theta\in(0,1)$, $9/16\le\alpha<1$ and $\mu=\alpha(1-\theta)+\theta$; let $\tilde C$ be the threshold (6) and $c^{DR}_1,c^{DR}_2$ the thresholds of scenario DR. Then for every production cost $0<c<a\mu/b$ subgame-perfect equilibria of scenarios OR, DA and DR exist, and for any such equilibria the retailer's equilibrium profits satisfy:
--
--   1. $\pi^{OR}_R<\pi^{DR}_R=\pi^{DA}_R$ for $0<c<\tilde C$;
--   2. $\pi^{DA}_R=\pi^{DR}_R<\pi^{OR}_R$ for $\tilde C<c<c^{DR}_1$;
--   3. $\pi^{DA}_R<\pi^{OR}_R<\pi^{DR}_R$ for $c^{DR}_1<c<c^{DR}_2$;
--   4. $\pi^{DA}_R<\pi^{DR}_R=\pi^{OR}_R$ for $c^{DR}_2<c<a\mu/b$.
--
--   As the production cost rises, the retailer's best choice moves from payment postponement (DA) to pricing postponement (OR), then to both postponements (DR, strictly best), and finally back to pricing postponement, where DR and OR coincide because the supplier no longer inflates production.
--
--   **Formalization Note** $\pi^k_R$ is the retailer's expected profit on the path of a subgame-perfect equilibrium of scenario $k$ (mission setting), not a closed-form expression. The page introduces $\tilde C$ as "the same threshold as introduced in Proposition 1", where it is an existential; Appendix C, (6), gives it explicitly and says it is the threshold of Propositions 1, 2, 4(R) and 5(O), so $\tilde C$ is instantiated by (6). The existence conjunct is part of the statement so that the comparison is not vacuous.
-- source:
--   Geng, Guo, Xiao, Yang, …, SSRN 3546872 (author version), p. 16, Proposition 2; App. C, (6), PDF p. 37, and proof of Propositions 1 and 2, PDF p. 38

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting

namespace YieldPostpone.Preference

/-- Proposition 2, p. 16: for `α ≥ 9/16`, subgame-perfect equilibria of OR, DA and DR exist at
every cost `0 < c < aμ/b`, and for any such equilibria the retailer's profits satisfy
(i) `π^OR_R < π^DR_R = π^DA_R` for `0 < c < C̃`;
(ii) `π^DA_R = π^DR_R < π^OR_R` for `C̃ < c < c^DR_1`;
(iii) `π^DA_R < π^OR_R < π^DR_R` for `c^DR_1 < c < c^DR_2`;
(iv) `π^DA_R < π^DR_R = π^OR_R` for `c^DR_2 < c < aμ/b`,
with `C̃` the threshold (6). -/
theorem proposition_2 (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    (∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
        (∃ σ : Profile, IsSPE P c .OR σ) ∧ (∃ σ : Profile, IsSPE P c .DA σ) ∧
          (∃ σ : Profile, IsSPE P c .DR σ)) ∧
    ∀ (c : ℝ) (σOR σDA σDR : Profile), 0 < c → c < P.a * μ P / P.b →
      IsSPE P c .OR σOR → IsSPE P c .DA σDA → IsSPE P c .DR σDR →
      (c < Ctil P →
          piR P c .OR σOR < piR P c .DR σDR ∧ piR P c .DR σDR = piR P c .DA σDA) ∧
      (Ctil P < c → c < cDR1 P →
          piR P c .DA σDA = piR P c .DR σDR ∧ piR P c .DR σDR < piR P c .OR σOR) ∧
      (cDR1 P < c → c < cDR2 P →
          piR P c .DA σDA < piR P c .OR σOR ∧ piR P c .OR σOR < piR P c .DR σDR) ∧
      (cDR2 P < c →
          piR P c .DA σDA < piR P c .DR σDR ∧ piR P c .DR σDR = piR P c .OR σOR) := by sorry

end YieldPostpone.Preference
