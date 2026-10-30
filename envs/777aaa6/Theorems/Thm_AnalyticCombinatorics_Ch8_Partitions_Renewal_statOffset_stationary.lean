-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Renewal_statOffset_stationary
-- name    : AnalyticCombinatorics.Ch8.Partitions.Renewal.statOffset_stationary
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:10:14.454279+00:00
-- url     : https://prove2.me/theorems/1d0c12e6-c9e6-402a-bcf2-f2e6735d662e
-- title:
--   Stationarity of a size-biased renewal offset law
-- statement:
--   Proves stationarity of a size-biased renewal offset law under IsIncrementLaw. This does not identify it with a stationary law of every finite killed partition window.
--
--   The full literal source contract is:
--
--   ```lean
--   lemma statOffset_stationary {p : ℕ → ℝ} (hl : IsIncrementLaw p)
--       (hsum : Summable (incrTail p)) (r' : ℕ) :
--       ∑' r, statOffset p r * resStep p r r' = statOffset p r'
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/RenewalStationary.lean#L47. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalCore
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalOffset
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RenewalOverlap
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# The reference measure π for the renewal residual chain (sector route)

The sector/Dirichlet route to the renewal Green lower bound needs a reference measure `π` on the
residual chain `resStep p` (RenewalOffset) for which the antisymmetric cut-flux is controlled.  The
crucial structural property is **stationarity**: for a stationary `π`, the cut-flux *divergence*
`divJ(x) = π_x·rowsum − ∑_y π_y K(y,x)` vanishes identically, so the divergence term of the exact cut
identity `aAnti = −½∑ divJ·f·g − ∑ Hcut·grad` drops and the sector reduces to the genuine crossing
variation.

This file constructs that reference measure as the already-built size-biased offset law
`statOffset p = incrTail p / incrMean p` (RenewalOverlap) and proves it is **stationary** for the
residual chain:

  `∑'_r statOffset p r · resStep p r r' = statOffset p r'`.

The residual row `r ↦ resStep p r r'` is supported on exactly `{0, r'+1}` (jump from `0`, or
deterministic descent from `r'+1`), so the `tsum` is a two-term sum; stationarity then follows from
the tail recurrence `incrTail p r' = p(r'+1) + incrTail p (r'+1)` and `statOffset p 0 = 1/μ`.

This is the reference-measure half of `erdos_rankdiff_sector_input`; the remaining sector input is the
quantitative crossing-variation (cut-flux) bound, which the sector route needs *instead* of a
rank-drop local limit (the latter being the documented floor-rank `⌊3√n⌋` obstruction).
-/

open Filter Topology BigOperators

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Renewal

theorem AnalyticCombinatorics.Ch8.Partitions.Renewal.statOffset_stationary {p : ℕ → ℝ} (hl : IsIncrementLaw p)
    (hsum : Summable (incrTail p)) (r' : ℕ) :
    ∑' r, statOffset p r * resStep p r r' = statOffset p r' := by sorry
