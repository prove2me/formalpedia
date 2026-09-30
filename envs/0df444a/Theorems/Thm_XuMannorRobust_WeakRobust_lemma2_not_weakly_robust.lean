-- Prove2me | Theorems.Thm_XuMannorRobust_WeakRobust_lemma2_not_weakly_robust
-- name    : XuMannorRobust.WeakRobust.lemma2_not_weakly_robust
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T15:59:42.415329+00:00
-- url     : https://prove2.me/theorems/f946d792-d75c-4ffb-a7f5-431a7f3e5827
-- title:
--   Lemma 2 — a method that is not weakly robust has a gap $\ge \epsilon^*$ with probability $\ge \delta^*$ infinitely often
-- statement:
--   Let $\mathcal Z$ be a measurable space with a probability measure $\mu$, $\mathcal H$ a set of hypotheses, $l : \mathcal H \times \mathcal Z \to [0, M]$ a loss measurable in its sample argument, $\mathcal A = \{\mathcal A^n\}$ a learning method and $\mathbf s^*$ a fixed sequence of training samples. Let $\mathbf t(n) \sim \mu^n$. If $\mathcal A$ is **not** weakly robust w.r.t. $\mathbf s^*$, then there exist $\epsilon^*, \delta^* > 0$ such that for infinitely many $n$
--
--   $$\Pr\Big( \big| L(\mathcal A_{\mathbf s^*(n)}, \mathbf t(n)) - L(\mathcal A_{\mathbf s^*(n)}, \mathbf s^*(n)) \big| \ge \epsilon^* \Big) \ge \delta^*. \qquad (8)$$
--
--   This is the first step of the necessity half of Theorem 8: failure of weak robustness is turned into a quantitative, recurring discrepancy between test and training average losses.
--
--   **Formalization Note** "For infinitely many $n$" is `∃ᶠ n in atTop`. The probability is the product measure `Measure.pi (fun _ : Fin n => μ)` of the event, compared in $[0,\infty]$ with `ENNReal.ofReal δ*`. The bound and measurability of the loss are carried as the paper's standing assumptions of the section; measurability is added.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 410, Lemma 2, Eq. (8)

import Mathlib
import Definitions.Def_XuMannorRobust_WeakRobust_WeaklyRobust

open MeasureTheory Filter

namespace XuMannorRobust.WeakRobust

/-- Xu & Mannor 2012, p. 410, Lemma 2: if the learning method `A` is not weakly robust w.r.t. the
training sequence `s*`, there are `ε*, δ* > 0` such that for infinitely many `n`,
`Pr(|L(A_{s*(n)}, t(n)) − L(A_{s*(n)}, s*(n))| ≥ ε*) ≥ δ*`, with `t(n) ∼ μⁿ`. -/
theorem lemma2_not_weakly_robust {Z H : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M) (hl_meas : ∀ h, Measurable (l h))
    (A : (n : ℕ) → (Fin n → Z) → H) (sStar : ℕ → Z)
    (hnot : ¬ WeaklyRobust μ l A sStar) :
    ∃ ε > 0, ∃ δ > 0, ∃ᶠ n in atTop,
      ENNReal.ofReal δ ≤ Measure.pi (fun _ : Fin n => μ)
        {t | ε ≤ |avgLoss l (A n (firstN sStar n)) t
          - avgLoss l (A n (firstN sStar n)) (firstN sStar n)|} := by sorry

end XuMannorRobust.WeakRobust
