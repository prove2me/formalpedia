-- Prove2me | Theorems.Thm_ZOGlobalLB_Supplement_theorem_A_1
-- name    : ZOGlobalLB.Supplement.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:52:31.470439+00:00
-- url     : https://prove2.me/theorems/35acb617-e1db-42fe-9f7f-bdac4d3cd402
-- title:
--   Theorem A.1 — Gaussian maximum and dyadic chaining
-- statement:
--   There is a universal constant $C>0$ with both of the following properties.
--
--   1. If $Z_1,\ldots,Z_K$ are centered jointly Gaussian variables with $\max_i\mathbb E Z_i^2\le v^2$, not necessarily independent, then
--
--      $$
--      \left\|\max_{i\le K}|Z_i|\right\|_{L^2}\le Cv\sqrt{\log(2K)}.
--      $$
--
--   2. If $(Z_t)_{t\in T}$ is a separable centered Gaussian process on a totally bounded metric space whose metric is $d_Z(t,t')=\|Z_t-Z_{t'}\|_{L^2}$, then, for every base point $t_0$,
--
--      $$
--      \left\|\sup_{t\in T}|Z_t|\right\|_{L^2}
--      \le C\left[\|Z_{t_0}\|_{L^2}+\int_0^{\operatorname{diam}(T,d_Z)}\sqrt{\log(2N(\eta))}\,d\eta\right].
--      $$
--
--   Here $N(\eta)$ is the covering number for the canonical metric.
--
--   Differences from the source:
--   - encoding: $L^2$ norms and the entropy integral as nonnegative extended quantities → $[0,\infty]$ lintegrals followed by the $1/2$ power; reason: preserves infinite values and avoids the Bochner integral's nonintegrable default
--   - encoding: a separable process → a countable index subset with the same absolute supremum almost surely; reason: this is the standard separable-version property and makes the supremum measurable without restricting null-set representatives
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Theorem A.1, pp.33-34

import Mathlib
import Definitions.Def_HighDimProb_RandomProcesses_CanonicalMetric
import Definitions.Def_HighDimProb_Chaining_CoveringNumber

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZOGlobalLB

namespace Supplement

/-- **Theorem A.1 (Gaussian maximum and dyadic chaining).** Xia, Yuan,
*On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization*, arXiv:2610.19652,
Theorem A.1, pp.33--34.

One universal constant simultaneously gives (i) the `L²` maximum bound for finitely many
centered, jointly Gaussian variables, without independence, and (ii) the `L²` absolute-supremum
Dudley bound for a separable centered Gaussian process on a totally bounded canonical metric
space, including the arbitrary base-point term and the entropy integral up to the diameter.

**Formalization Note.** `L²` norms and the entropy integral are valued in `ℝ≥0∞`, preserving an
infinite value rather than using the Bochner integral's default zero. `IsGaussianProcess` means
all finite-dimensional marginals are jointly Gaussian. Process separability is stated by the
standard almost-sure countable-supremum property. The ambient metric is required
to equal the published canonical `L²` metric. Total boundedness makes the covering number finite at
every positive scale and also prevents `Metric.diam` from taking its unbounded-set junk value. -/
theorem theorem_A_1 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (K : ℕ), 0 < K → ∀ (Ω : Type) [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P] (Z : Fin K → Ω → ℝ) (v₀ : ℝ), 0 ≤ v₀ →
        IsGaussianProcess Z P →
        (∀ i, Integrable (Z i) P ∧ ∫ ω, Z i ω ∂P = 0 ∧
          ∫⁻ ω, ENNReal.ofReal ((Z i ω) ^ 2) ∂P ≤ ENNReal.ofReal (v₀ ^ 2)) →
        (∫⁻ ω, (⨆ i : Fin K, ENNReal.ofReal |Z i ω|) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal C * ENNReal.ofReal v₀ *
            ENNReal.ofReal (Real.sqrt (Real.log (2 * K)))) ∧
      (∀ (T : Type) [MetricSpace T] [Nonempty T]
        (htot : TotallyBounded (Set.univ : Set T))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : T → Ω → ℝ), IsGaussianProcess Z P →
        (∀ t, Integrable (Z t) P ∧ ∫ ω, Z t ω ∂P = 0 ∧
          Integrable (fun ω => (Z t ω) ^ 2) P) →
        (∀ t s, dist t s = HighDimProb.RandomProcesses.canonicalMetric P Z t s) →
        (∃ D : Set T, D.Countable ∧ ∀ᵐ ω ∂P,
          (⨆ t : T, ENNReal.ofReal |Z t ω|) =
            ⨆ t : D, ENNReal.ofReal |Z t.1 ω|) →
        ∀ t₀ : T,
          (∫⁻ ω, (⨆ t : T, ENNReal.ofReal |Z t ω|) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
            ENNReal.ofReal C *
              ((∫⁻ ω, ENNReal.ofReal ((Z t₀ ω) ^ 2) ∂P) ^ (1 / 2 : ℝ) +
                ∫⁻ η in Set.Ioc 0 (Metric.diam (Set.univ : Set T)),
                  if HighDimProb.Chaining.coveringNumber T η = ⊤ then ⊤
                  else ENNReal.ofReal (Real.sqrt (Real.log
                    (2 * (HighDimProb.Chaining.coveringNumber T η).toNat))))) := by sorry

end Supplement

end ZOGlobalLB
