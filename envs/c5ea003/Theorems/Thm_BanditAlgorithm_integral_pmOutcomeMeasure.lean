-- Prove2me | Theorems.Thm_BanditAlgorithm_integral_pmOutcomeMeasure
-- name    : BanditAlgorithm.integral_pmOutcomeMeasure
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T20:27:58.840594+00:00
-- url     : https://prove2.me/theorems/65f6197d-91f9-4ce0-a7ef-392105c1b58d
-- title:
--   Expectation under a finite categorical outcome measure
-- statement:
--   Let $p$ be a probability vector on a finite set and let $P_p$ be its categorical probability measure. Then every real-valued function $g$ has expectation
--
--   $$
--   \int g(i)\,dP_p(i)=\sum_i p_i g(i).
--   $$
--
--   This is the integration rule that turns one-step action expectations under Algorithm 26 into finite weighted sums. The simplex hypothesis supplies nonnegative masses summing to one, including the finiteness needed by the Bochner integral.
-- source:
--   Finite categorical expectation identity; used implicitly throughout Lattimore and Szepesvári, Bandit Algorithms (2020), proof of Theorem 37.15, printed pp. 494–495, https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringStochastic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory
open scoped BigOperators ENNReal

namespace BanditAlgorithm

theorem integral_pmOutcomeMeasure
    {d : ℕ} (p : Fin d → ℝ) (hp : p ∈ stdSimplex ℝ (Fin d))
    (g : Fin d → ℝ) :
    ∫ i, g i ∂pmOutcomeMeasure p = ∑ i, p i * g i := by sorry
