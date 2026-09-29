-- Prove2me | Theorems.Thm_Erdos146_badPairLayersRetentionEvent_real_le
-- name    : Erdos146.badPairLayersRetentionEvent_real_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:49:43.064694+00:00
-- url     : https://prove2.me/theorems/8a8ed000-8978-4181-88da-b4ef35075508
-- title:
--   The bad-array event has small probability (Lemma 7.1)
-- statement:
--   **Lemma 7.1 (Exclusion of low-entropy arrays).** The probability that some layer admits a parent array together with a pairwise distinct retained child array of entropy at most $\beta - \delta$ is at most $2s\,2^{-m}$. The exclusion argument runs on the conditional-entropy functional $E(u,z) = \frac{1}{m}\sum_{j=1}^{m} H(Z_j \mid X_j, Y_j)$ of Section 7, where a parent pair is drawn uniformly and oriented by an independent fair coin. The thresholds are $A(\tau) = \kappa + \tau\log_2 3$ and $C(\tau) = 2h(\tau) - 1$, and the construction needs a sampling exponent $\beta$ with $A(\tau) < \beta < C(\tau)$. The count of arrays of conditional entropy $E$ is at most $2^{mME + O(m\log_2 M)}$, while requiring all $M = \binom{L}{2}$ children to survive sampling costs $2^{-\beta mM}$; since $M \asymp L^2$ this dominates the $2^{mL}$ parent arrays whenever $E < \beta$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L15686-L15742

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Real

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.badPairLayersRetentionEvent_real_le
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
        (badPairLayersRetentionEvent layerSizes dimension) ≤
      (((2 * depth : ℕ) : ℝ)) *
        Real.exp (-(dimension : ℝ) * Real.log 2) := by sorry
