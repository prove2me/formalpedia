-- Prove2me | Theorems.Thm_WorstCaseCVaR_Discrete_minmax_inequality
-- name    : WorstCaseCVaR.Discrete.minmax_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:49.649519+00:00
-- url     : https://prove2.me/theorems/0e3289b9-1405-437e-9288-8a94a672d12a
-- title:
--   Proof of Theorem 2 (via the proof of Theorem 1) — min-max inequality $\mathrm{WCVaR}_\beta(x) \le \sup_{\pi} G_\beta(x,\alpha,\pi)$ for every $\alpha$
-- statement:
--   Let $f$, the scenarios $y_{[1]},\dots,y_{[S]}$, the decision $x$ and $G_\beta$, $\mathrm{CVaR}_\beta$, $\mathrm{WCVaR}_\beta$ be as in the setting of §2.2, with $0<\beta<1$, and let $\mathcal P_\pi$ be a nonempty set of probability vectors in $\mathbb R^S$. Then for every $\alpha \in \mathbb R$
--   $$\mathrm{WCVaR}_\beta(x) = \sup_{\pi\in\mathcal P_\pi}\min_{\alpha'\in\mathbb R} G_\beta(x,\alpha',\pi) \;\le\; \sup_{\pi\in\mathcal P_\pi} G_\beta(x,\alpha,\pi).$$
--   Equivalently,
--   $$\inf_{\alpha\in\mathbb R}\sup_{\pi\in\mathcal P_\pi} G_\beta(x,\alpha,\pi) \;\ge\; \sup_{\pi\in\mathcal P_\pi}\min_{\alpha\in\mathbb R} G_\beta(x,\alpha,\pi).$$
--
--   This is the elementary min-max inequality (weak duality) on the unrestricted threshold line $\mathbb R$; together with the saddle point on $\mathcal A \times \mathcal P_\pi$ it closes the gap between $\inf_{\alpha\in\mathbb R}$ and $\min_{\alpha\in\mathcal A}$ in the proof of Theorem 2. The paper prints it in the proof of Theorem 1 for the mixture function $H_\beta$ and invokes it for $G_\beta$ through "a further discussion similar to the proof of Theorem 1".
--
--   **Formalization Note** The inequality is stated pointwise in $\alpha$, which is equivalent to the inf form. The suprema are real `sSup`s of images; for a nonempty set of probability vectors and $0<\beta<1$ both images are nonempty and bounded above, so they are true suprema. Compactness of $\mathcal P_\pi$ is not needed for this inequality and is not assumed.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1167, proof of Theorem 1 (min-max inequality), as used in the proof of Theorem 2

import Mathlib
import Definitions.Def_WorstCaseCVaR_Discrete_Setting

namespace WorstCaseCVaR.Discrete

/-- The min-max inequality used in the proof of Theorem 2, Zhu & Fukushima (2009), p. 1167 (stated
there for Theorem 1's `H_β`): `inf_{α ∈ ℝ} max_{π ∈ 𝒫_π} G_β(x, α, π) ≥ sup_{π ∈ 𝒫_π} min_{α ∈ ℝ}
G_β(x, α, π) = WCVaR_β(x)`, in the equivalent form: for every `α`,
`WCVaR_β(x) ≤ max_{π ∈ 𝒫_π} G_β(x, α, π)`. -/
theorem minmax_inequality {n m S : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (ys : Fin S → Fin m → ℝ) (x : Fin n → ℝ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (P : Set (Fin S → ℝ)) (hP : P ⊆ stdSimplex ℝ (Fin S)) (hne : P.Nonempty) :
    ∀ α : ℝ, wcvar f ys β x P ≤ sSup ((fun π => G f ys β x α π) '' P) := by sorry

end WorstCaseCVaR.Discrete
