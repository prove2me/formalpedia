-- Prove2me | Theorems.Thm_DAREx_RescaledErrorMoments
-- name    : DAREx.RescaledErrorMoments
-- status  : Open
-- author  : @Minghui
-- created : 2026-09-29T06:03:13.139909+00:00
-- url     : https://prove2.me/theorems/3c5cb77c-cc9e-48cf-825a-379d6b187d53
-- title:
--   Rescaled pruning — exact bias, variance, and mean square
-- statement:
--   **Notation.** $\Omega=\{0,1\}^n$ is the finite space of Bernoulli drop masks; $n$ is the number of coordinates and $p$ is the drop probability. Coefficients are fixed before drawing the mask. For any $n\ge0$, fixed coefficients $c_j\in\mathbb R$, $0\le p\le1$, and $q>0$, draw independent Bernoulli($p$) drop indicators $\omega_j$. Put $H_q=\sum_jc_j(1-(1-\omega_j)/q)$, $S=\sum_jc_j$, $Q=\sum_jc_j^2$, and $b_q=(1-(1-p)/q)S$. Then $$\mathbb EH_q=b_q,\qquad\mathbb E(H_q-b_q)^2=\frac{p(1-p)}{q^2}Q,$$ $$\mathbb EH_q^2=b_q^2+\frac{p(1-p)}{q^2}Q.$$ Expectations are finite product-mask sums. **Formalization note:** paper-derived extension of the DARE moment calculation to the general $1/q$ rescaling model; this does not assert the optimizer or tail formula later printed in Appendix E.2. Empty vectors and deterministic endpoint masks are included.
--
--   **Source:** Deng et al., DARE the Extreme: Revisiting Delta-Parameter Pruning For Fine-Tuned Models, ICLR 2025, arXiv:2410.09344v2, https://arxiv.org/pdf/2410.09344v2, Section 3.2, PDF p. 5, equation (2); Appendix E.1, PDF p. 29, initial unnumbered mean/variance calculations; Appendix E.2, PDF p. 31, initial unnumbered general-rescaling identity.
-- source:
--   Deng et al., DARE the Extreme: Revisiting Delta-Parameter Pruning For Fine-Tuned Models, ICLR 2025, arXiv:2410.09344v2, https://arxiv.org/pdf/2410.09344v2, Section 3.2, PDF p. 5, equation (2); Appendix E.1, PDF p. 29, initial unnumbered mean/variance calculations; Appendix E.2, PDF p. 31, initial unnumbered general-rescaling identity.

import Definitions.Def_DAREx_Model

namespace DAREx
theorem RescaledErrorMoments :
  ∀ (n : ℕ) (c : Fin n → ℝ) (p q : ℝ), 0 ≤ p → p ≤ 1 → 0 < q →
    mean p (outputError q c) = outputBias p q c ∧
    mean p (fun ω ↦ (outputError q c ω - outputBias p q c) ^ 2) =
      p * (1 - p) / q ^ 2 * energy c ∧
    mean p (fun ω ↦ outputError q c ω ^ 2) =
      outputBias p q c ^ 2 + p * (1 - p) / q ^ 2 * energy c := by sorry
end DAREx
