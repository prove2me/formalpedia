-- Prove2me | Theorems.Thm_Erdos146_manuscriptSamplingFailureEvent_real_le
-- name    : Erdos146.manuscriptSamplingFailureEvent_real_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:53:04.554973+00:00
-- url     : https://prove2.me/theorems/f52bc124-5848-46ac-96cd-b938741f57cd
-- title:
--   The sampling-failure event has small probability
-- statement:
--   Step in the exclusion argument of Sections 7 and 8. The exclusion argument runs on the conditional-entropy functional $E(u,z) = \frac{1}{m}\sum_{j=1}^{m} H(Z_j \mid X_j, Y_j)$ of Section 7, where a parent pair is drawn uniformly and oriented by an independent fair coin. The thresholds are $A(\tau) = \kappa + \tau\log_2 3$ and $C(\tau) = 2h(\tau) - 1$, and the construction needs a sampling exponent $\beta$ with $A(\tau) < \beta < C(\tau)$. Lemma 7.1 excludes, with probability at least $1 - 2s\,2^{-m}$, any parent array of length $L_{i-1}$ together with a pairwise distinct retained child array of length $L_i$ satisfying $E(u,z) \le \beta - \delta$. Under the manuscript's parameter choice, the total probability that sampling fails to deliver a dense $H$-free graph is bounded as stated.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L17847-L17913

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Real

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.manuscriptSamplingFailureEvent_real_le
    {depth dimension : ℕ}
    (layerSizes : Fin depth → ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, 4 ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        3 * logTwo
          (((layerSizes layer).choose 2 + 1 : ℕ) : ℝ) -
          entropySlack * ((layerSizes layer).choose 2 : ℝ) < -1) :
    (hammingRetentionMeasure dimension).real
      (manuscriptSamplingFailureEvent layerSizes dimension) ≤
        manuscriptSamplingFailureBound depth dimension := by sorry
