-- Prove2me | Theorems.Thm_DAREx_DAREOutputConcentration
-- name    : DAREx.DAREOutputConcentration
-- status  : Open
-- author  : @Minghui
-- created : 2026-09-29T06:14:04.22799+00:00
-- url     : https://prove2.me/theorems/d3296345-6939-45d7-a96f-3fa2c1c27058
-- title:
--   Appendix E.1, equation (8) — DARE output concentration
-- statement:
--   **Notation.** $\Omega=\{0,1\}^n$ is the finite space of Bernoulli drop masks; $n$ is the number of coordinates and $p$ is the drop probability. Coefficients are fixed before drawing the mask. For $n>0$, fix any real influence coefficients $c_j=\Delta W_jx_j$. Set $\bar c=n^{-1}\sum_jc_j$ and $\sigma^2=n^{-1}\sum_j(c_j-\bar c)^2$. Let $0<p<1$ be the drop probability and $0<\gamma<1$ the allowed failure probability. Draw independent Bernoulli($p$) drop indicators $\omega_j$ and define $H=\sum_jc_j(1-(1-\omega_j)/(1-p))$. Put $\Phi(1/2)=1/2$ and $\Phi(p)=(1-2p)/\log((1-p)/p)$ otherwise. Then $$\Pr\left\{|H|\le\frac{\sqrt{\Phi(p)}}{1-p}\sqrt{n(\bar c^2+\sigma^2)}\sqrt{\log(2/\gamma)}\right\}\ge1-\gamma.$$ There is no nonzero-coefficient or positive-energy hypothesis. **Formalization note:** equation (8), using the source's coefficient-energy identity, with an explicit continuous value at $p=1/2$. This is not the piecewise formula printed in Theorem 3.1: the missing square root and the one-sided high-pruning refinement are not imported. The mission description explains the distinction.
--
--   **Source:** Deng et al., DARE the Extreme: Revisiting Delta-Parameter Pruning For Fine-Tuned Models, ICLR 2025, arXiv:2410.09344v2, https://arxiv.org/pdf/2410.09344v2, Appendix E.1, PDF p. 30, equation (8); PDF p. 31, unnumbered coefficient-energy identity; Section 3.2, PDF p. 5, equation (2) and Theorem 3.1 notation.
-- source:
--   Deng et al., DARE the Extreme: Revisiting Delta-Parameter Pruning For Fine-Tuned Models, ICLR 2025, arXiv:2410.09344v2, https://arxiv.org/pdf/2410.09344v2, Appendix E.1, PDF p. 30, equation (8); PDF p. 31, unnumbered coefficient-energy identity; Section 3.2, PDF p. 5, equation (2) and Theorem 3.1 notation.

import Definitions.Def_DAREx_Model

namespace DAREx
theorem DAREOutputConcentration :
  ∀ (n : ℕ) (c : Fin n → ℝ) (p γ : ℝ),
    0 < n → 0 < p → p < 1 → 0 < γ → γ < 1 →
    1 - γ ≤ probability p (fun ω ↦ |dareError p c ω| ≤
      Real.sqrt (phi p) / (1 - p) *
        Real.sqrt ((n : ℝ) * (empiricalMean c ^ 2 + empiricalVariance c)) *
        Real.sqrt (Real.log (2 / γ))) := by sorry
end DAREx
