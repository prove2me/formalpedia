-- Prove2me | Theorems.Thm_mme_child_partition_rate_sum_bound
-- name    : mme_child_partition_rate_sum_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:57:47.824533+00:00
-- url     : https://prove2.me/theorems/e6251ee5-a63b-4633-8b52-407f0889c9ec
-- title:
--   Arbitrary child partitions retain the total rate bound
-- statement:
--   Pointwise lower bounds for the boundary and interior parts of any finite partition imply a lower bound for their total rate, with one explicit loss per original cell. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_boundary_normalized_weight_rate_bound
open scoped BigOperators

theorem mme_child_partition_rate_sum_bound {C : Type*} [Fintype C]
    (nB nI : ℕ) (e : (Fin nB ⊕ Fin nI) ≃ C)
    (q : C → ℝ) (b : Fin nB → ℝ) (i : Fin nI → ℝ)
    (scale loss : ℝ)
    (hb : ∀ r, scale * (q (e (.inl r)) - loss) ≤ b r)
    (hi : ∀ r, scale * (q (e (.inr r)) - loss) ≤ i r) :
    scale * ((∑ c, q c) - (Fintype.card C : ℝ) * loss) ≤
      (∑ r, b r) + ∑ r, i r := by sorry
