-- Prove2me | Theorems.Thm_XuMannorRobust_Standard_bretagnolle_huber_carol
-- name    : XuMannorRobust.Standard.bretagnolle_huber_carol
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T15:32:13.4053+00:00
-- url     : https://prove2.me/theorems/e4773e88-04b6-4ece-b36f-959f70f4d9fd
-- title:
--   Proof of Theorem 1: $\Pr\{\sum_i ||N_i|/n - \mu(C_i)| \ge \lambda\} \le 2^K e^{-n\lambda^2/2}$ (Bretagnolle–Huber–Carol)
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\mathcal Z$ and let $C_1, \dots, C_K$ be a partition of $\mathcal Z$ into $K$ pairwise disjoint measurable sets. Draw a training set $\mathbf s = (s_1, \dots, s_n)$ of $n \ge 1$ i.i.d. samples from $\mu$ and let $|N_i|$ be the number of samples falling in $C_i$. Then for every $\lambda \ge 0$,
--
--   $$\Pr\left\{\sum_{i=1}^K \left| \frac{|N_i|}{n} - \mu(C_i) \right| \ge \lambda \right\} \le 2^K \exp\left(\frac{-n\lambda^2}{2}\right).$$
--
--   This is the Bretagnolle–Huber–Carol inequality for the multinomial vector $(|N_1|, \dots, |N_K|)$ (van der Vaart and Wellner 2000, Proposition A.6.6), which Xu and Mannor invoke in the proof of Theorem 1. It controls the $\ell_1$ distance between the empirical and the true cell probabilities uniformly in the partition's geometry: only the number of cells $K$ enters.
--
--   **Formalization Note** The probability is the outer measure of the event under the product measure $\mu^n$ on `Fin n → Z`. The hypothesis $\lambda \ge 0$ is added: for $\lambda < 0$ the event is everything while the right side can be below $1$, and the paper uses the inequality only at $\lambda > 0$. $\mu(C_i)$ is taken as a real number (`ENNReal.toReal`), which is exact for a probability measure.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 396, proof of Theorem 1 (Bretagnolle–Huber–Carol display; van der Vaart & Wellner 2000, Prop. A6.6)

import Mathlib
import Definitions.Def_XuMannorRobust_Standard_CellCount

open MeasureTheory

namespace XuMannorRobust.Standard

/-- **Bretagnolle–Huber–Carol inequality** as used in the proof of Theorem 1 (Xu & Mannor 2012,
p. 396; van der Vaart–Wellner 2000, Prop. A.6.6). For a measurable partition `C_1, …, C_K` of `Z`,
`n ≥ 1` i.i.d. draws from a probability measure `μ` and `λ ≥ 0`,
`Pr{∑_i ||N_i|/n − μ(C_i)| ≥ λ} ≤ 2^K exp(−nλ²/2)`. The probability is the outer measure of the
event under `μⁿ`. The hypothesis `λ ≥ 0` is added (the display is false for `λ < 0`). -/
theorem bretagnolle_huber_carol {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {K : ℕ} (C : Fin K → Set Z) (hC_meas : ∀ i, MeasurableSet (C i))
    (hC_disj : Pairwise (Function.onFun Disjoint C)) (hC_cover : (⋃ i, C i) = Set.univ)
    {n : ℕ} (hn : 0 < n) (lam : ℝ) (hlam : 0 ≤ lam) :
    (Measure.pi fun _ : Fin n => μ)
        {s | lam ≤ ∑ i, |(cellCount C s i : ℝ) / (n : ℝ) - (μ (C i)).toReal|}
      ≤ ENNReal.ofReal ((2 : ℝ) ^ K * Real.exp (-((n : ℝ) * lam ^ 2) / 2)) := by sorry

end XuMannorRobust.Standard
