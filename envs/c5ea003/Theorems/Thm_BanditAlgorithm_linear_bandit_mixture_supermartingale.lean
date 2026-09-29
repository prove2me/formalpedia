-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_mixture_supermartingale
-- name    : BanditAlgorithm.linear_bandit_mixture_supermartingale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T00:15:25.825647+00:00
-- url     : https://prove2.me/theorems/7aa5f247-bcd9-4a60-9afd-884c02e60083
-- statement:
--   (Supermartingale property, L&S Lemmas 20.2 and 20.3) On a standard Borel probability space with filtration $\mathcal{F}$, let the actions $A_{t+1} : \Omega \to \mathbb{R}^d$ be $\mathcal{F}_t$-measurable and the noise $\eta_{t+1}$ be $\mathcal{F}_{t+1}$-measurable and conditionally 1-subgaussian given $\mathcal{F}_t$ (Eq. 20.4:
--
--   $$\mathbb{E}[\exp(\alpha\,\eta_{t+1}) \mid \mathcal{F}_t] \le \exp(\alpha^2/2) \ \text{a.s. for all } \alpha;$$
--
--   Mathlib's `HasCondSubgaussianMGF` with $c = 1$). Fix $\lambda \ge 0$ and let
--
--   $$M_t(x) = \exp\Big(\langle x, S_t\rangle - \tfrac{1}{2}\|x\|^2_{V_t(\lambda)}\Big).$$
--
--   Then:
--
--   - (i) for every $x \in \mathbb{R}^d$, $(M_t(x))_t$ is a nonnegative $\mathcal{F}$-supermartingale with $M_0(x) = \exp(-\lambda\|x\|^2/2) \le 1$;
--   - (ii) for every probability measure $h$ on $\mathbb{R}^d$ under which the mixture integrals $x \mapsto M_t(x)(\omega)$ are $h$-integrable, the mixture $\bar M_t = \int M_t(x)\,dh(x)$ is a nonnegative $\mathcal{F}$-supermartingale with $\bar M_0 \le 1$, and $\bar M_0 = 1$ in the unregularized case $\lambda = 0$ treated by the book.
-- source:
--   L&S Lemmas 20.2 (p.257) and 20.3 (p.259)

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Martingale.Basic
import Definitions.Def_SelfNormalizedProcess


open MeasureTheory ProbabilityTheory Matrix

theorem BanditAlgorithm.linear_bandit_mixture_supermartingale
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {lam : ℝ} (hlam : 0 ≤ lam)
    (h : Measure (Fin d → ℝ)) [IsProbabilityMeasure h]
    (hInt : ∀ (t : ℕ) (ω : Ω),
      Integrable (fun x => selfNormalizedProcess d lam η A x t ω) h) :
    (∀ x : Fin d → ℝ,
      Supermartingale (selfNormalizedProcess d lam η A x) ℱ P ∧
        ∀ ω : Ω, selfNormalizedProcess d lam η A x 0 ω ≤ 1) ∧
    Supermartingale
      (fun (t : ℕ) (ω : Ω) => ∫ x, selfNormalizedProcess d lam η A x t ω ∂h) ℱ P ∧
    (∀ ω : Ω, (∫ x, selfNormalizedProcess d lam η A x 0 ω ∂h) ≤ 1) ∧
    (lam = 0 → ∀ ω : Ω, (∫ x, selfNormalizedProcess d lam η A x 0 ω ∂h) = 1) := by
  sorry
