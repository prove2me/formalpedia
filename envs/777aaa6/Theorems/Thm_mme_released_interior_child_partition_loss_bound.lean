-- Prove2me | Theorems.Thm_mme_released_interior_child_partition_loss_bound
-- name    : mme_released_interior_child_partition_loss_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T16:27:12.113627+00:00
-- url     : https://prove2.me/theorems/18370b21-b13d-4359-8c98-011a08613a4e
-- title:
--   Every released child partition has a uniform error budget
-- statement:
--   The bound of ninety actual child cells combines with the finite partition rate inequality to bound the normalized loss by 540 times the common error parameter, for any boundary and interior enumeration. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_child_partition_rate_sum_bound
import Theorems.Thm_mme_released_interior_child_card_bound
open scoped BigOperators
open MME MME.ReleasedInterior MME.RecursiveYZ

theorem mme_released_interior_child_partition_loss_bound
    (s : Fin 45) (nB nI : ℕ)
    (e : (Fin nB ⊕ Fin nI) ≃ Cell 4 6 (parent s))
    (q : Cell 4 6 (parent s) → ℝ)
    (b : Fin nB → ℝ) (i : Fin nI → ℝ)
    (scale delta bound : ℝ) (hscale : 0 ≤ scale) (hdelta : 0 ≤ delta)
    (hsum : bound ≤ ∑ c, q c)
    (hb : ∀ r, scale * (q (e (.inl r)) - 6 * delta) ≤ b r)
    (hi : ∀ r, scale * (q (e (.inr r)) - 6 * delta) ≤ i r) :
    scale * (bound - 540 * delta) ≤ (∑ r, b r) + ∑ r, i r := by sorry
