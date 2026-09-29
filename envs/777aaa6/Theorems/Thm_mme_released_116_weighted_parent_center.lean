-- Prove2me | Theorems.Thm_mme_released_116_weighted_parent_center
-- name    : mme_released_116_weighted_parent_center
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:12:43.275317+00:00
-- url     : https://prove2.me/theorems/05432ca2-6739-4457-b736-87e7e8e7c538
-- title:
--   The released (1,1,6) center is the weighted mean of its integer parent mixtures
-- statement:
--   Let $H_i(w)$ be the exact mode-$i$ full-word histogram of the released owner-zero $(1,1,6)$ joint row. For its six integer regions, let $n_r$ be the regional size and $P_{r,i}$ the parent mixture computed from the prescribed split counts and child profiles. With $d=10^{12}$ and the literal split $w=w_L\mathbin{\|}w_R$,
--   $$\frac{H_i(w)}{d^4}=\sum_{r=0}^{5}\frac{n_r}{d^4}P_{r,i}(w_L,w_R).$$
--   Thus the released normalized center is exactly the regional-size-weighted mean of the concrete integer parent centers. This is the center identity used to aggregate regional histogram windows; coordinate partitions and tolerance estimates are separate requirements.
-- source:
--   Released owner-zero term010, jointRows 0 10, and the concrete integer regional profiles.

import Definitions.Def_mme_released_116_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

theorem mme_released_116_weighted_parent_center
    (i : Fin 3) (w : CompleteWord 3) :
    (∑ r : Fin 6, ((regionalSize r : ℝ) / (denominator : ℝ) ^ 4) *
      RegionRealization.parentMixture parent_total regionalSize splitCount
        (integerProfile i) r
        ![((completeWordSplitEquiv 2 (by decide)) w).1,
          ((completeWordSplitEquiv 2 (by decide)) w).2]) =
      ((((ReleasedGlobal.jointRows 0 10).map
        (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
        (denominator : ℝ) ^ 4 := by sorry
