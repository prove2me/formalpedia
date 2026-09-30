-- Prove2me | Theorems.Thm_XuMannorRobust_Quantile_eventE_cell_deviation_bound
-- name    : XuMannorRobust.Quantile.eventE_cell_deviation_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T16:16:08.384986+00:00
-- url     : https://prove2.me/theorems/35c0ecf1-15a1-4692-9184-6f24c01b970d
-- title:
--   Appendix C, the event $\mathcal E$ — $\sum_i \big||N_i|/n - \mu(C_i)\big| \le \lambda_0$ with probability at least $1-\delta$
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\mathcal Z$ and let $C_1, \dots, C_K$ be a partition of $\mathcal Z$ into measurable sets. Let $\mathbf s = (s_1, \dots, s_n)$, $n \ge 1$, consist of $n$ i.i.d. draws from $\mu$, and let $N_i = \{ j : s_j \in C_i \}$ be the set of indices of the points of $\mathbf s$ that fall into $C_i$. For $\delta > 0$ let $\mathcal E$ be the event
--
--   $$\sum_{i=1}^K \left| \frac{|N_i|}{n} - \mu(C_i) \right| \le \sqrt{\frac{2K \ln 2 + 2 \ln(1/\delta)}{n}}.$$
--
--   Then $\Pr(\mathcal E) \ge 1 - \delta$.
--
--   On $\mathcal E$ the empirical cell frequencies are uniformly close to the cell probabilities; the proof of Theorem 5 works entirely on this event.
--
--   **Formalization Note** "Probability at least $1-\delta$" is encoded as: the outer measure under the product measure $\mu^n$ of the set of training sets on which the inequality fails is at most $\delta$; the outer measure makes a measurability statement about that set unnecessary. Indices run over $\{0, \dots, n-1\}$. This is Eq. (3) of the paper's proof of Theorem 1, restated in this mission's namespace.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, pp. 415–416, Appendix C (Proof of Theorem 5), definition of the event E and Pr(E) ≥ 1 − δ (from Eq. (3), p. 397)

import Mathlib

open MeasureTheory

namespace XuMannorRobust.Quantile

open Classical in
/-- **The event ℰ** (Xu & Mannor 2012, pp. 415–416, Appendix C, proof of Theorem 5). For a
measurable partition `C_1, …, C_K` of `Z`, `n ≥ 1` i.i.d. draws `s` from a probability measure `μ`
and `δ > 0`, let `N_i = {j : s_j ∈ C_i}`. Then `Pr(ℰ) ≥ 1 − δ`, where `ℰ` is the event
`∑_i ||N_i|/n − μ(C_i)| ≤ √((2K ln 2 + 2 ln(1/δ))/n)`: the outer measure under `μⁿ` of the
complement of `ℰ` is at most `δ`. -/
theorem eventE_cell_deviation_bound {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {K : ℕ} (C : Fin K → Set Z) (hC_meas : ∀ i, MeasurableSet (C i))
    (hC_disj : Pairwise (Function.onFun Disjoint C)) (hC_cover : (⋃ i, C i) = Set.univ)
    {n : ℕ} (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => μ)
        {s : Fin n → Z | ¬ (∑ i, |((Finset.univ.filter fun j => s j ∈ C i).card : ℝ) / (n : ℝ)
              - (μ (C i)).toReal|
            ≤ Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)))}
      ≤ ENNReal.ofReal δ := by sorry

end XuMannorRobust.Quantile
