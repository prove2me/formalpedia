-- Prove2me | Theorems.Thm_DAREx_DAREExponentialTail
-- name    : DAREx.DAREExponentialTail
-- status  : Open
-- author  : @Minghui
-- created : 2026-09-29T06:10:52.043072+00:00
-- url     : https://prove2.me/theorems/d7ac7bac-7a7c-4084-b4a8-4584aa769192
-- title:
--   Appendix E.1 — exponential tail for DARE output error
-- statement:
--   **Notation.** $\Omega=\{0,1\}^n$ is the finite space of Bernoulli drop masks; $n$ is the number of coordinates and $p$ is the drop probability. Coefficients are fixed before drawing the mask. Fix $n\ge0$, deterministic $c\in\mathbb R^n$, $0<p<1$, energy $Q=\sum_jc_j^2>0$, and $t>0$. Draw independent Bernoulli($p$) drop indicators and let $H=\sum_jc_j(1-(1-\omega_j)/(1-p))$. With $\Phi$ defined by the logarithmic quotient and $\Phi(1/2)=1/2$, $$\Pr(|H|>t)\le2\exp\left(-\frac{t^2(1-p)^2}{\Phi(p)Q}\right).$$ **Formalization note:** direct source tail formula with explicit positive energy for its denominator; strict $>t$ matches the source. Arbitrary signed coefficients are allowed. The main confidence-bound goal separately includes the zero-energy case.
--
--   **Source:** Deng et al., DARE the Extreme: Revisiting Delta-Parameter Pruning For Fine-Tuned Models, ICLR 2025, arXiv:2410.09344v2, https://arxiv.org/pdf/2410.09344v2, Section 3.2, PDF p. 5, equation (2); Appendix E.1, PDF p. 30, unnumbered tail display immediately preceding equation (8), from Theorem E.1, PDF p. 29, equations (6)–(7).
-- source:
--   Deng et al., DARE the Extreme: Revisiting Delta-Parameter Pruning For Fine-Tuned Models, ICLR 2025, arXiv:2410.09344v2, https://arxiv.org/pdf/2410.09344v2, Section 3.2, PDF p. 5, equation (2); Appendix E.1, PDF p. 30, unnumbered tail display immediately preceding equation (8), from Theorem E.1, PDF p. 29, equations (6)–(7).

import Definitions.Def_DAREx_Model

namespace DAREx
theorem DAREExponentialTail :
  ∀ (n : ℕ) (c : Fin n → ℝ) (p t : ℝ),
    0 < p → p < 1 → 0 < energy c → 0 < t →
    probability p (fun ω ↦ t < |dareError p c ω|) ≤
      2 * Real.exp (-(t ^ 2 * (1 - p) ^ 2 / (phi p * energy c))) := by sorry
end DAREx
