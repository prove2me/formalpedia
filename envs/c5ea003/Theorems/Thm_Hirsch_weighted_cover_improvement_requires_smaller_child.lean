-- Prove2me | Theorems.Thm_Hirsch_weighted_cover_improvement_requires_smaller_child
-- name    : Hirsch.weighted_cover_improvement_requires_smaller_child
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T23:11:35.907328+00:00
-- url     : https://prove2.me/theorems/599aaead-0333-4d91-8bc5-d7e3e8b9831a
-- title:
--   Averaging improvement requires a child better than vertex counting
-- statement:
--   Let $V$ be a finite set covered by finite subsets $F_i$ with nonnegative integer weights $w_i$, so every element receives covering weight at least $q>0$. Let $B_i$ be nonnegative integers. If the averaging certificate
--   $$\left\lfloor\frac{\sum_i w_i(B_i+1)}q\right\rfloor-1$$
--   is strictly less than $|V|-1$, then some positively weighted subset satisfies $B_i+1<|F_i|$. Division and subtraction are the natural-number operations. This is a finite counting theorem: it bounds what an averaging certificate can achieve, not an actual polytope diameter. No geometric or graph assumption is implicit.
-- source:
--   https://github.com/jjoshua2/prove2me-work/blob/681314640b6f84792d8ae011c3534a6e8c456930/Solutions/PolynomialFaceCoverBarrier.lean ; declaration HirschFaceCoverBarrier.improving_certificate_requires_improving_child; pinned CI run 34532572816.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

namespace Hirsch

theorem weighted_cover_improvement_requires_smaller_child {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (F : ι → Finset V) (B weight : ι → ℕ) (q : ℕ) (hq : 0 < q)
    (hcover : ∀ v, q ≤ ∑ i, if v ∈ F i then weight i else 0)
    (hsmall : (∑ i, weight i * (B i + 1)) / q - 1 < Fintype.card V - 1) :
    ∃ i, 0 < weight i ∧ B i + 1 < (F i).card := by sorry

end Hirsch
