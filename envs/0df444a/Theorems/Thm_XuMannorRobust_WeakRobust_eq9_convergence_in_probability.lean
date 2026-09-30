-- Prove2me | Theorems.Thm_XuMannorRobust_WeakRobust_eq9_convergence_in_probability
-- name    : XuMannorRobust.WeakRobust.eq9_convergence_in_probability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:02:50.636015+00:00
-- url     : https://prove2.me/theorems/5492e618-9c7b-40bd-9bc4-4bb0b87f44b4
-- title:
--   Eq. (9) — test average loss converges in probability to the expected loss
-- statement:
--   Let $\mathcal Z$ be a measurable space with a probability measure $\mu$, $\mathcal H$ a set of hypotheses, $l : \mathcal H \times \mathcal Z \to [0, M]$ a loss measurable in its sample argument, $\mathcal A = \{\mathcal A^n\}$ a learning method and $\mathbf s^*$ a fixed sequence of training samples. Let $\mathbf t(n) \sim \mu^n$. Then
--
--   $$L(\mathcal A_{\mathbf s^*(n)}, \mathbf t(n)) - \mathcal L(\mathcal A_{\mathbf s^*(n)}) \xrightarrow{\ \Pr\ } 0, \qquad (9)$$
--
--   that is, for every $\epsilon > 0$,
--
--   $$\lim_{n \to \infty} \Pr\Big( \big| L(\mathcal A_{\mathbf s^*(n)}, \mathbf t(n)) - \mathcal L(\mathcal A_{\mathbf s^*(n)}) \big| \ge \epsilon \Big) = 0.$$
--
--   The hypothesis $\mathcal A_{\mathbf s^*(n)}$ changes with $n$; the convergence holds because the loss is uniformly bounded by $M$, so the concentration is uniform over hypotheses. Combined with Lemma 2 it gives the necessity half of Theorem 8.
--
--   **Formalization Note** The probability is `Measure.pi (fun _ : Fin n => μ)` of the event, and the limit is in $[0, \infty]$. Measurability of $l(h, \cdot)$ is added.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 411, proof of Theorem 8, Eq. (9)

import Mathlib
import Definitions.Def_XuMannorRobust_WeakRobust_Setup

open MeasureTheory Filter Topology

namespace XuMannorRobust.WeakRobust

/-- Xu & Mannor 2012, p. 411, proof of Theorem 8, Eq. (9): for a loss uniformly bounded in
`[0, M]`, `L(A_{s*(n)}, t(n)) − 𝓛(A_{s*(n)}) → 0` in probability, `t(n) ∼ μⁿ`: for every `ε > 0`,
`Pr(|L(A_{s*(n)}, t(n)) − 𝓛(A_{s*(n)})| ≥ ε) → 0`. The hypothesis `A_{s*(n)}` changes with `n`. -/
theorem eq9_convergence_in_probability {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    (A : (n : ℕ) → (Fin n → Z) → H) (sStar : ℕ → Z) :
    ∀ ε > 0, Tendsto
      (fun n => Measure.pi (fun _ : Fin n => μ)
        {t | ε ≤ |avgLoss l (A n (firstN sStar n)) t - expectedLoss μ l (A n (firstN sStar n))|})
      atTop (𝓝 0) := by sorry

end XuMannorRobust.WeakRobust
