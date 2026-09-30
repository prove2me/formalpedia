-- Prove2me | Theorems.Thm_XuMannorRobust_WeakRobust_theorem8_sufficiency_bound
-- name    : XuMannorRobust.WeakRobust.theorem8_sufficiency_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T15:56:15.258618+00:00
-- url     : https://prove2.me/theorems/31690b4d-cec9-43fe-a9df-9554588a0cf0
-- title:
--   Proof of Theorem 8 — generalization gap at most $\delta M + \epsilon$
-- statement:
--   Let $\mathcal Z$ be a measurable space with a probability measure $\mu$, $\mathcal H$ a set of hypotheses, and $l : \mathcal H \times \mathcal Z \to [0, M]$ a loss measurable in its sample argument. Let $n \ge 1$, $h \in \mathcal H$, $\mathbf s \in \mathcal Z^n$ and $\mathcal D \subseteq \mathcal Z^n$, and let $\delta, \epsilon \ge 0$. Let $\mathbf t(n) \sim \mu^n$. Suppose
--
--   1. $\Pr(\mathbf t(n) \notin \mathcal D) \le \delta$, and
--   2. $|L(h, \hat{\mathbf s}) - L(h, \mathbf s)| \le \epsilon$ for every $\hat{\mathbf s} \in \mathcal D$.
--
--   Then
--
--   $$\big| \mathcal L(h) - L(h, \mathbf s) \big| \le \delta M + \epsilon.$$
--
--   This is the finite-$n$ inequality behind the sufficiency half of Theorem 8: applied with $h = \mathcal A_{\mathbf s^*(n)}$, $\mathbf s = \mathbf s^*(n)$ and the sets $\mathcal D_n$ of weak robustness, it shows that the generalization gap is eventually at most $\delta M + \epsilon$ for arbitrary $\delta, \epsilon > 0$.
--
--   **Formalization Note** The paper has $\Pr(\mathbf t(n) \in \mathcal D_n) > 1 - \delta$ and a strict bound $< \epsilon$ in (7); the hypotheses here are the non-strict forms, which are weaker, so the statement is stronger and still the paper's inequality. The probability of the complement is `Measure.pi (fun _ : Fin n => μ) Dᶜ`, the outer measure when $\mathcal D$ is not measurable. Measurability of $l(h, \cdot)$ is added.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 410, proof of Theorem 8, sufficiency display (bound δM + ϵ)

import Mathlib
import Definitions.Def_XuMannorRobust_WeakRobust_Setup

open MeasureTheory

namespace XuMannorRobust.WeakRobust

/-- Xu & Mannor 2012, p. 410, proof of Theorem 8 (sufficiency display): if a set `D ⊆ Zⁿ` has
`Pr(t(n) ∉ D) ≤ δ` and every `ŝ ∈ D` has `|L(h, ŝ) − L(h, s)| ≤ ε`, then
`|𝓛(h) − L(h, s)| ≤ δ M + ε`, for a loss measurable with values in `[0, M]` and `n ≥ 1`. -/
theorem theorem8_sufficiency_bound {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 0 < n) (h : H) (s : Fin n → Z) (D : Set (Fin n → Z))
    (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hD : Measure.pi (fun _ : Fin n => μ) Dᶜ ≤ ENNReal.ofReal δ)
    (hDε : ∀ t ∈ D, |avgLoss l h t - avgLoss l h s| ≤ ε) :
    |expectedLoss μ l h - avgLoss l h s| ≤ δ * M + ε := by sorry

end XuMannorRobust.WeakRobust
