-- Prove2me | Theorems.Thm_DAREx_KearnsSaulMGF
-- name    : DAREx.KearnsSaulMGF
-- status  : Proved
-- author  : @Minghui
-- created : 2026-09-29T06:08:02.745191+00:00
-- url     : https://prove2.me/theorems/d384aa62-fd26-4739-9089-8a6a761e66f5
-- title:
--   Kearns–Saul inequality — both exponential-moment directions
-- statement:
--   **Notation.** $B$ is a Bernoulli random variable, $p=\Pr(B=1)$, $t$ is an arbitrary real exponential-moment parameter, and $\Phi$ is defined below. For $0<p<1$, let $\Phi(p)=(1-2p)/\log((1-p)/p)$ when $p\ne1/2$, and $\Phi(1/2)=1/2$. Then $0<\Phi(p)\le1/2$, and for every real $t$, $$ (1-p)e^{-tp}+pe^{t(1-p)}\le\exp(\Phi(p)t^2/4).$$ The left side is the exponential moment of a centered Bernoulli($p$) variable. Both signs of $t$ are part of the conclusion. **Formalization note:** explicitly sourced external analytic input, specialized to the open probability interval needed by DARE, together with the source's coefficient bound. The half-probability value is the removable-singularity extension in the proof of Berend–Kontorovich Theorem 4. It is not the one-sided refinement in Lemma 5.
--
--   **Source:** Deng et al., DARE the Extreme: Revisiting Delta-Parameter Pruning For Fine-Tuned Models, ICLR 2025, arXiv:2410.09344v2, https://arxiv.org/pdf/2410.09344v2, Appendix E.1, PDF p. 29, Theorem E.1 and equations (6)–(7); PDF p. 30, bounds on Phi following equation (8). Berend and Kontorovich, On the Concentration of the Missing Mass, https://arxiv.org/pdf/1210.3248v1, Section 3, PDF p. 3, Theorem 4, equation (6), proof PDF pp. 3–4.
-- source:
--   Deng et al., DARE the Extreme: Revisiting Delta-Parameter Pruning For Fine-Tuned Models, ICLR 2025, arXiv:2410.09344v2, https://arxiv.org/pdf/2410.09344v2, Appendix E.1, PDF p. 29, Theorem E.1 and equations (6)–(7); PDF p. 30, bounds on Phi following equation (8). Berend and Kontorovich, On the Concentration of the Missing Mass, https://arxiv.org/pdf/1210.3248v1, Section 3, PDF p. 3, Theorem 4, equation (6), proof PDF pp. 3–4.

import Definitions.Def_DAREx_Model

namespace DAREx
theorem KearnsSaulMGF :
  ∀ p : ℝ, 0 < p → p < 1 →
    0 < phi p ∧ phi p ≤ 1 / 2 ∧
    ∀ t : ℝ, (1 - p) * Real.exp (-t * p) + p * Real.exp (t * (1 - p)) ≤
      Real.exp (phi p * t ^ 2 / 4) := by sorry
end DAREx
