-- Prove2me | Theorems.Thm_XuMannorRobust_Standard_Supplement_theorem2
-- name    : XuMannorRobust.Standard.Supplement.theorem2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:00:09.435544+00:00
-- url     : https://prove2.me/theorems/31ba1899-01aa-4920-93dc-2c0e85b44055
-- title:
--   Theorem 2 — robust quantile and truncated-mean brackets (corrected: Definition 3 conventions)
-- statement:
--   Let $Z$ be a measurable sample space, $H$ a hypothesis set and $l:H\times Z\to[0,M]$ a loss with measurable sections. Let $n\ge1$, $\mu$ be a probability measure, $A:Z^n\to H$ a $(K,\epsilon(\cdot))$-robust learner with a fixed measurable partition, and $\mu_{\rm emp}$ the empirical measure counting all observations with multiplicity. Fix $\delta>0$ and $\beta\in(0,1)$, put
--
--   $$\lambda_0=\sqrt{\frac{2K\ln2+2\ln(1/\delta)}{n}},\qquad 0\le\beta-\lambda_0\le\beta+\lambda_0\le1.$$
--
--   With probability at least $1-\delta$ under $\mu^n$, both brackets hold on the same event:
--
--   $$Q(A_s,\beta-\lambda_0,\mu_{\rm emp})-\epsilon(s)\le Q(A_s,\beta,\mu)\le Q(A_s,\beta+\lambda_0,\mu_{\rm emp})+\epsilon(s),$$
--   $$T(A_s,\beta-\lambda_0,\mu_{\rm emp})-\epsilon(s)\le T(A_s,\beta,\mu)\le T(A_s,\beta+\lambda_0,\mu_{\rm emp})+\epsilon(s).$$
--
--   Here $Q$ is the loss quantile and $T$ the unnormalized left-tail truncated mean. This companion theorem extends robust generalization to distributional summaries of loss; the published Theorem 5 supplies its pseudo-robust generalization.
--
--   **Formalization Note** Both shifted endpoints may equal zero or one. The published Definition 3's atom correction and zero-level conventions are retained. All positive confidence parameters are allowed; for $\delta\ge1$ the outer-probability assertion is automatic. Real square roots use Lean's nonnegative square root.
--
--   Differences from the source:
--   - encoding: the paper ignores measurability → each loss section and every fixed partition cell is measurable; reason: restores the intended probability and expectation setting; bounded measurable losses are integrable, without assuming the algorithm or epsilon measurable
--   - encoding: with probability at least 1 minus delta → the outer measure of the bad event is at most delta; reason: a fixed measurable concentration event controls all learners pointwise, so no measurable learner or epsilon premise is required
--   - encoding: a training sample of positive size n with repeated observations → Fin n indexed tuples with n positive and all counts retaining multiplicity; reason: zero samples make the source averages undefined; real casts precede division and subtraction
--   - correction: Definition 3 divides the atom correction by its atom probability and leaves the zero quantile as an unbounded infimum → the published corrected truncated mean omits that division and assigns zero to the zero-level quantile and truncated mean; reason: the p. 399 worked example and Appendix C identify the atom correction; nonnegative losses make the lower bracket at level zero automatic; the published definitions remain unchanged; with equiprobable losses 1 and 2, n=10000, beta=1/2 and delta=10^(-8), the balanced empirical sample has probability at least 1/10001>delta but the printed upper truncated bracket reads 1≤1/2+4lambda<1 (see SOURCE_CORRECTION.md)
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 400, Theorem 2; §4.1 and Appendix C, pp. 415–418; Definition 3, p. 399 (published corrected convention).

import Mathlib
import Definitions.Def_XuMannorRobust_Standard_IsRobust
import Definitions.Def_XuMannorRobust_Quantile_LossQuantile

open MeasureTheory XuMannorRobust.Quantile

namespace XuMannorRobust.Standard.Supplement

/-- Theorem 2, both parts on the same event. The published corrected truncated
mean and zero-level convention are reused without alteration. -/
theorem theorem2 {Z H : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M)
    (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 0 < n) (A : (Fin n → Z) → H)
    (K : ℕ) (ε : (Fin n → Z) → ℝ) (hA : IsRobust l A K ε)
    (δ : ℝ) (hδ : 0 < δ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hlevels : 0 ≤ β - Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)) ∧
      β - Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)) ≤
        β + Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)) ∧
      β + Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)) ≤ 1) :
    (Measure.pi fun _ : Fin n => μ) {s : Fin n → Z | ¬
      ((lossQuantile l (A s)
          (β - Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)))
          (empiricalMeasure s) - ε s ≤ lossQuantile l (A s) β μ ∧
        lossQuantile l (A s) β μ ≤ lossQuantile l (A s)
          (β + Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)))
          (empiricalMeasure s) + ε s) ∧
       (lossTruncatedMean l (A s)
          (β - Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)))
          (empiricalMeasure s) - ε s ≤ lossTruncatedMean l (A s) β μ ∧
        lossTruncatedMean l (A s) β μ ≤ lossTruncatedMean l (A s)
          (β + Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ)))
          (empiricalMeasure s) + ε s))} ≤ ENNReal.ofReal δ := by sorry

end XuMannorRobust.Standard.Supplement
