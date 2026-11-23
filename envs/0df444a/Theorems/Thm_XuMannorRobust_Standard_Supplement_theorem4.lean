-- Prove2me | Theorems.Thm_XuMannorRobust_Standard_Supplement_theorem4
-- name    : XuMannorRobust.Standard.Supplement.theorem4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:01:32.693777+00:00
-- url     : https://prove2.me/theorems/cf069fcc-7d73-4e9b-98df-9e68490fa3fb
-- title:
--   Theorem 4 — pseudo-robust expected-loss bound
-- statement:
--   Let $Z$ be a measurable sample space, $H$ a hypothesis set and $l:H\times Z\to[0,M]$ a loss with measurable sections. Let $n\ge1$, $\mu$ be a probability measure and $A:Z^n\to H$ be $(K,\epsilon(\cdot),\hat n(\cdot))$ pseudo robust in Definition 5. The partition is fixed before the sample; its measurable cells cover $Z$. The number $\hat n(s)\in\{1,\ldots,n\}$ counts a sample-dependent subset of indices, so duplicate observations count separately.
--
--   For every $\delta>0$, with probability at least $1-\delta$ under $\mu^n$,
--
--   $$\left|\mathcal L_\mu(A_s)-l_{\rm emp}(A_s)\right|\le\frac{\hat n(s)}{n}\epsilon(s)+M\left(\frac{n-\hat n(s)}{n}+\sqrt{\frac{2K\ln2+2\ln(1/\delta)}{n}}\right).$$
--
--   This companion theorem permits robustness to fail at part of the training data, with the uncovered fraction charged explicitly. At full coverage it recovers the robust expected-loss estimate.
--
--   **Formalization Note** The coverage remains a function of the entire sample. Subtraction takes place after casting to the reals; its value is nonnegative because the reused predicate includes $\hat n(s)\le n$. No measurability of the algorithm, coverage function or error function is imposed. All $\delta>0$ are included, with $\delta\ge1$ automatic.
--
--   Differences from the source:
--   - encoding: the paper ignores measurability → each loss section and every fixed partition cell is measurable; reason: restores the intended probability and expectation setting; bounded measurable losses are integrable, without assuming the algorithm or epsilon measurable
--   - encoding: with probability at least 1 minus delta → the outer measure of the bad event is at most delta; reason: a fixed measurable concentration event controls all learners pointwise, so no measurable learner or epsilon premise is required
--   - encoding: a training sample of positive size n with repeated observations → Fin n indexed tuples with n positive and all counts retaining multiplicity; reason: zero samples make the source averages undefined; real casts precede division and subtraction
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 401, Theorem 4; Definition 5, p. 401; Appendix B, pp. 414–415.

import Mathlib
import Definitions.Def_XuMannorRobust_Standard_Losses
import Definitions.Def_XuMannorRobust_Quantile_IsPseudoRobust

open MeasureTheory XuMannorRobust.Quantile

namespace XuMannorRobust.Standard.Supplement

/-- Theorem 4: pseudo-robust expected loss, with sample-dependent coverage. -/
theorem theorem4 {Z H : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M)
    (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 0 < n) (A : (Fin n → Z) → H)
    (K : ℕ) (ε : (Fin n → Z) → ℝ) (nhat : (Fin n → Z) → ℕ)
    (hA : IsPseudoRobust l A K ε nhat) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => μ) {s : Fin n → Z | ¬
      (|expectedLoss μ l (A s) - empiricalLoss l (A s) s| ≤
        ((nhat s : ℝ) / (n : ℝ)) * ε s + M *
          (((n : ℝ) - (nhat s : ℝ)) / (n : ℝ) +
            Real.sqrt ((2 * (K : ℝ) * Real.log 2 + 2 * Real.log (1 / δ)) / (n : ℝ))))}
      ≤ ENNReal.ofReal δ := by sorry

end XuMannorRobust.Standard.Supplement
