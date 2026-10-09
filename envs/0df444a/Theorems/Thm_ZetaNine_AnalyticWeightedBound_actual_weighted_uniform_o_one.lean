-- Prove2me | Theorems.Thm_ZetaNine_AnalyticWeightedBound_actual_weighted_uniform_o_one
-- name    : ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-08T14:55:46.25753+00:00
-- url     : https://prove2.me/theorems/99ee3a6f-7b0e-4bd9-9771-6d70987fcfb0
-- title:
--   Actual quartic-weighted kernel: coefficient-uniform exponential decay
-- statement:
--   For the actual factorial rational kernel $R_n$ and every rational polynomial $W$ of degree at most four, there is one error sequence $\varepsilon_n\to0$, independent of $W$, such that
--
--   $$\left|\sum_{m\ge0}W((m+1)(m+1+n))R_n(m+1)\right|\le e^{(-2641/250+\varepsilon_n)n}\sum_{r=0}^4 |W_r|n^{2r}\qquad(n\ge1).$$
--
--   This is an upper bound for the genuine infinite sum and allows arbitrary changing rational quartics. The complete proof establishes the true moments and summability rather than assuming either. It provides analytic decay; it does not construct short integer outputs, prove the lattice margin J, or assert irrationality. The rate is the certified rational lower precision used by the local analytic proof, not a claim of the exact saddle exponent.
-- source:
--   Local zeta(9) research: research/analytic-weighted-uniform-source-delta-2026-10-07.md; complete original factorial, actual-moment, phase and quartic proof chain in the submitted Lean file. Native and fresh platform independent validation completed 2026-10-08.

import Definitions.Def_ZetaNine_AnalyticUniformWeighted
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine
open ZetaNine.AnalyticMomentBounds ZetaNine.AnalyticUniformMomentBound
open ZetaNine.AnalyticWeightedBound

namespace ZetaNine.AnalyticWeightedBound
theorem actual_weighted_uniform_o_one :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * weightedCoefficientHeight n W := by sorry
end ZetaNine.AnalyticWeightedBound
