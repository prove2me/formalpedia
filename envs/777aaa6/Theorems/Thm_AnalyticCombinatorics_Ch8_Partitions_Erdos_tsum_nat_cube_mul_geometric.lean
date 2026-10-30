-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_tsum_nat_cube_mul_geometric
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_nat_cube_mul_geometric
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:51:02.528376+00:00
-- url     : https://prove2.me/theorems/622145f3-cac7-49a3-975b-cdd6488d538f
-- title:
--   A cubic geometric-series identity
-- statement:
--   For every real $y$ with $|y|<1$, $$\sum_{n=0}^{\infty}n^3y^n=\frac{y(1+4y+y^2)}{(1-y)^4}.$$ The index includes zero. This is a series identity rather than a partition asymptotic.
--
--   This support estimate carries the following complete literal source contract:
--
--   ```lean
--   lemma tsum_nat_cube_mul_geometric {y : ℝ} (hy : ‖y‖ < 1) :
--       ∑' n : ℕ, ((n : ℝ)) ^ 3 * y ^ n = y * (1 + 4 * y + y ^ 2) / (1 - y) ^ 4
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/MassRateGeom3.lean#L24. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Mass-rate campaign: the cubic geometric sum (M₂-side ingredient)

`Σ'_{n} n³·yⁿ = y(1+4y+y²)/(1−y)⁴` — via
`n³ = 6·C(n+3,3) − 12·C(n+2,2) + 7·C(n+1,1) − C(n,0)`
(verified: n=1: 24−36+14−1=1 ✓, n=2: 60−72+21−1=8 ✓) over Mathlib's choose-geometric
sums; closed form check: `6 − 12(1−y) + 7(1−y)² − (1−y)³ = y(1+4y+y²)` ✓.
Opus-authored.
-/

set_option maxHeartbeats 800000

open Filter Finset
open scoped BigOperators Topology

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.tsum_nat_cube_mul_geometric {y : ℝ} (hy : ‖y‖ < 1) :
    ∑' n : ℕ, ((n : ℝ)) ^ 3 * y ^ n = y * (1 + 4 * y + y ^ 2) / (1 - y) ^ 4 := by sorry
