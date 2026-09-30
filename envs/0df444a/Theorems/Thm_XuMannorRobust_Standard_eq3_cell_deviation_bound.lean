-- Prove2me | Theorems.Thm_XuMannorRobust_Standard_eq3_cell_deviation_bound
-- name    : XuMannorRobust.Standard.eq3_cell_deviation_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T15:33:57.594831+00:00
-- url     : https://prove2.me/theorems/bbfb108d-8207-4515-9a75-e387199ae611
-- title:
--   Eq. (3): w.p. $\ge 1-\delta$, $\sum_i ||N_i|/n - \mu(C_i)| \le \sqrt{(2K\ln 2 + 2\ln(1/\delta))/n}$
-- statement:
--   Let $\mu$ be a probability measure on a measurable space $\mathcal Z$, let $C_1, \dots, C_K$ be a partition of $\mathcal Z$ into $K$ pairwise disjoint measurable sets, and let $\mathbf s = (s_1,\dots,s_n)$ be $n \ge 1$ i.i.d. draws from $\mu$, with $|N_i|$ the number of draws in $C_i$. Then for every $\delta > 0$, with probability at least $1-\delta$,
--
--   $$\sum_{i=1}^K \left| \frac{|N_i|}{n} - \mu(C_i) \right| \le \sqrt{\frac{2K\ln 2 + 2\ln(1/\delta)}{n}}.$$
--
--   This is Eq. (3) in the proof of Theorem 1 of Xu and Mannor: the Bretagnolle–Huber–Carol inequality solved for the deviation level at confidence $1-\delta$. It is the only probabilistic ingredient of Theorem 1.
--
--   **Formalization Note** "With probability at least $1-\delta$" is stated as: the outer measure under $\mu^n$ of the set of training sets violating the inequality is at most $\delta$; no measurability of that set is needed. For $\delta > 2^K$ the radicand is negative and Lean's square root returns $0$; the statement remains true there (and trivial for $\delta \ge 1$), so no upper bound on $\delta$ is imposed.
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 397, proof of Theorem 1, Eq. (3)

import Mathlib
import Definitions.Def_XuMannorRobust_Standard_CellCount

open MeasureTheory

namespace XuMannorRobust.Standard

/-- **Eq. (3)** (Xu & Mannor 2012, p. 397, proof of Theorem 1). For a measurable partition
`C_1, …, C_K` of `Z`, `n ≥ 1` i.i.d. draws from a probability measure `μ` and `δ > 0`, with
probability at least `1 − δ`,
`∑_i ||N_i|/n − μ(C_i)| ≤ √((2K ln 2 + 2 ln(1/δ))/n)`: the outer measure under `μⁿ` of the set
where this fails is at most `δ`. -/
theorem eq3_cell_deviation_bound {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    [IsProbabilityMeasure μ] {K : ℕ} (C : Fin K → Set Z) (hC_meas : ∀ i, MeasurableSet (C i))
    (hC_disj : Pairwise (Function.onFun Disjoint C)) (hC_cover : (⋃ i, C i) = Set.univ)
    {n : ℕ} (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => μ)
        {s | ¬ (∑ i, |(cellCount C s i : ℝ) / (n : ℝ) - (μ (C i)).toReal|
            ≤ Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)))}
      ≤ ENNReal.ofReal δ := by sorry

end XuMannorRobust.Standard
