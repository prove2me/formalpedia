-- Prove2me | Theorems.Thm_avram_dividend_classical_renewal_quotient_limit_le_pointwise_upper_bound_fa7e49e3
-- name    : avram_dividend_classical_renewal_quotient_limit_le_pointwise_upper_bound_fa7e49e3
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:10:15.749005+00:00
-- url     : https://prove2.me/theorems/8b6da141-80a1-4435-8690-901ddbc9ba51
-- title:
--   Avram dividend classical renewal quotient limit le: Pointwise upper bound
-- statement:
--   At every point covered by the stated hypotheses, the left-hand expression is at most the right-hand expression.

import Mathlib
open Filter Topology
open scoped ENNReal

theorem avram_dividend_classical_renewal_quotient_limit_le_pointwise_upper_bound_fa7e49e3 (V : ℝ≥0∞) (W : ℝ → ℝ) (a d : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W d a) (hd : d ≠ 0)
    (hWa : 0 < W a)
    (hW8 : ∀ ε : ℝ, 0 < ε → ε < a → 0 ≤ W (a - ε))
    (hlt : ∀ ε : ℝ, 0 < ε → ε < a → W (a - ε) < W a)
    (hfin : ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < a →
      ∑ k ∈ Finset.range N,
        ENNReal.ofReal ε * (ENNReal.ofReal (W (a - ε) / W a)) ^ (k + 1) ≤ V) 
    (hWa0 : W a ≠ 0)
    : ∀ ε : ℝ, 0 < ε → ε < a →
      ENNReal.ofReal (ε * (W (a - ε) / W a) / (1 - W (a - ε) / W a)) ≤ V := by sorry
