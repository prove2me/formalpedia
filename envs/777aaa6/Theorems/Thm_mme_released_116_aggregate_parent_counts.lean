-- Prove2me | Theorems.Thm_mme_released_116_aggregate_parent_counts
-- name    : mme_released_116_aggregate_parent_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:10:05.343492+00:00
-- url     : https://prove2.me/theorems/c77aebb0-c949-4132-9999-da6c39026ce5
-- title:
--   Released (1,1,6) mode counts aggregate the six regional child products
-- statement:
--   For the released owner-zero $(1,1,6)$ component, let $J(a)$ be its exact joint atom counts, $b_r$ the six region weights, $a_{r,c}$ their split weights, and $u_{r,c,i}$ their square-child marginal counts. For every mode $i$ and full word $w=w_L\mathbin{\|}w_R$,
--   $$\sum_{a:\,\operatorname{atom}(a)_i=w}J(a)=\sum_{r=0}^{5}b_r\sum_c a_{r,c}\,u_{r,c,i}(w_L)\,u_{r,\bar c,i}(w_R).$$
--   The halves are the literal complete-word split, and $\bar c=(1,1,6)-c$. Both sides are exact integers at scale $d^4$, where $d=10^{12}$. This connects the released full-word mode histogram with the regional centers before frequency normalization.
-- source:
--   Released owner-zero term010, jointRows 0 10, and the literal complete-word split.

import Definitions.Def_mme_released_116_integer_profiles
import Definitions.Def_mme_complete_split_concatenation

open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

theorem mme_released_116_aggregate_parent_counts :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      ((ReleasedGlobal.jointRows 0 10).map
        (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
      ∑ r : Fin 6, seed.region.getD r.val 0 *
        ∑ c : Released116.Split, splitWeight r c *
          childMarginal r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
          childMarginal r (complement (parent_total r) c) i
            ((completeWordSplitEquiv 2 (by decide)) w).2 := by sorry
