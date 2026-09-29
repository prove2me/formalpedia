-- Prove2me | Theorems.Thm_TreatmentLocality_memLp_rwd_of_invariant
-- name    : TreatmentLocality.memLp_rwd_of_invariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T03:14:41.10071+00:00
-- url     : https://prove2.me/theorems/3df74a69-5568-452c-9a40-513b9fc46228
-- title:
--   Square-integrability of the reward under an invariant experiment law
-- statement:
--   **Square-integrability of the reward along a stationary experiment.** As above, but with second moments: if each of the finitely many reward laws of the SST model of arXiv:2407.19618 is square-integrable — as it is for Gaussian rewards — then under any invariant law $\nu$ of the experiment chain,
--   $$\mathbb{E}_\nu\bigl[\,r^2\,\bigr] < \infty .$$
--
--   Invariance reduces the second moment to an average of one-step second moments, and the one-step law at any state is a fair mixture of two of the finitely many reward laws, so the bound is uniform in the state. This is what places the influence function of the information-sharing estimator in $L^2$, which is where the Cramér-Rao comparison takes place.
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, §2-§3 (the SST model, the mixed policy π^{1/2} and the experiment trajectory) and Appendix EC.3.1 (the stationary law of the experiment chain and its moment assumptions).

import Definitions.Def_TreatmentLocality
import Definitions.Def_MarkovIterKernel
import Mathlib.Probability.Kernel.Invariance

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.memLp_rwd_of_invariant {S : Type*} [DecidableEq S] [Fintype S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (M : Model S)
    (ν : Measure (Step S)) [IsProbabilityMeasure ν]
    (hinv : Kernel.Invariant (expKernel M) ν)
    (hR2 : ∀ t a, MemLp (fun r : ℝ => r) 2 (M.reward t a)) :
    MemLp (fun z : Step S => Step.rwd z) 2 ν := by sorry
