-- Prove2me | Theorems.Thm_XuMannorRobust_Standard_Supplement_theorem3
-- name    : XuMannorRobust.Standard.Supplement.theorem3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:01:01.718695+00:00
-- url     : https://prove2.me/theorems/825fd92b-41b6-4e0c-9d1a-0369cec4d32c
-- title:
--   Theorem 3 — generalization from a Doeblin chain
-- statement:
--   Let $Z$ be an arbitrary measurable space, $H$ a hypothesis set and $P$ a homogeneous probability transition kernel satisfying Definition 4 with $\alpha>0$ and integer $T\ge1$. Let $l:H\times Z\to[0,M]$ have measurable sections and let $A:Z^n\to H$ be $(K,\epsilon(\cdot))$ robust with a fixed measurable partition. Assume $n>2T/\alpha$ and fix any $\delta>0$.
--
--   There exists an invariant probability $\pi$ for $P$. For every such $\pi$ and every initial probability law $\rho$, the first $n$ observations $s$ of the chain satisfy, with probability at least $1-\delta$,
--
--   $$\left|\mathcal L_\pi(A_s)-l_{\rm emp}(A_s)\right|\le\epsilon(s)+M\left\{\frac{2T}{\alpha n}+\sqrt{\frac{2T^2(K\ln2+\ln(1/\delta))}{\alpha^2 n}}\right\}.$$
--
--   The population loss $\mathcal L_\pi$ is expectation under the invariant probability, whereas $\rho$ is the distribution of the first observed state. This companion theorem permits dependent observations on general state spaces without a stationary-start assumption.
--
--   **Formalization Note** Invariant-law existence is retained as a conclusion from the governing text at p. 401, rather than an extra premise. `chainPrefixLaw` is the actual path-prefix probability, not an IID product. Neither countability, topology, reversibility nor stationary initialization is assumed. The threshold implies $n>0$, and the positivity of $\alpha$ guards every denominator. All $\delta>0$ are included; when $\delta\ge1$ the probability claim is automatic. Appendix A's incorrect identification of the full cell $\ell_1$ deviation with the union supremum is not a hypothesis or a target; the printed theorem constant is retained.
--
--   Differences from the source:
--   - encoding: the paper ignores measurability → each loss section and every fixed partition cell is measurable; reason: restores the intended probability and expectation setting; bounded measurable losses are integrable, without assuming the algorithm or epsilon measurable
--   - encoding: with probability at least 1 minus delta → the outer measure of the bad event is at most delta; reason: a fixed measurable concentration event controls all learners pointwise, so no measurable learner or epsilon premise is required
--   - encoding: the first n outputs of a Doeblin chain and its invariant measure → Mathlib trajectory prefix law indexed from zero, with invariant probability existence and the bound for every initial probability; reason: the governing text at p. 401 asserts invariant-law existence; reindexing the first observation changes no chain or starting distribution
-- source:
--   Xu & Mannor, Robustness and Generalization, Mach Learn 86 (2012), DOI 10.1007/s10994-011-5268-1, p. 401, Theorem 3; Definition 4, p. 400; invariant probability, p. 401; Appendix A, pp. 413–414.

import Mathlib
import Definitions.Def_XuMannorRobust_Standard_Losses
import Definitions.Def_XuMannorRobust_Standard_IsRobust
import Definitions.Def_XuMannorRobust_Standard_Supplement_DoeblinChain

open MeasureTheory ProbabilityTheory

namespace XuMannorRobust.Standard.Supplement

/-- Theorem 3 with the governing invariant-law existence assertion retained.
The bound is for any invariant probability and any initial probability law.
Appendix A's erroneous L1/union-sup identity is not assumed. -/
theorem theorem3 {Z H : Type*} [MeasurableSpace Z]
    (P : Kernel Z Z) [IsMarkovKernel P] (α : ℝ) (T : ℕ)
    (hP : IsDoeblin P α T)
    (l : H → Z → ℝ) (M : ℝ)
    (hl_bound : ∀ h z, 0 ≤ l h z ∧ l h z ≤ M)
    (hl_meas : ∀ h, Measurable (l h))
    {n : ℕ} (hn : 2 * (T : ℝ) / α < (n : ℝ))
    (A : (Fin n → Z) → H) (K : ℕ) (ε : (Fin n → Z) → ℝ)
    (hA : IsRobust l A K ε) (δ : ℝ) (hδ : 0 < δ) :
    (∃ π : Measure Z, IsProbabilityMeasure π ∧ P.Invariant π) ∧
    ∀ (π : Measure Z), IsProbabilityMeasure π → P.Invariant π →
      ∀ (ρ : Measure Z), IsProbabilityMeasure ρ →
        chainPrefixLaw P ρ n {s : Fin n → Z | ¬
          (|expectedLoss π l (A s) - empiricalLoss l (A s) s| ≤ ε s + M *
            (2 * (T : ℝ) / (α * (n : ℝ)) +
              Real.sqrt ((2 * (T : ℝ) ^ 2 * ((K : ℝ) * Real.log 2 + Real.log (1 / δ))) /
                (α ^ 2 * (n : ℝ)))))} ≤ ENNReal.ofReal δ := by sorry

end XuMannorRobust.Standard.Supplement
