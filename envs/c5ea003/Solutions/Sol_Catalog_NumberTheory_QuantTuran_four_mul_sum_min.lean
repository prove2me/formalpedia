-- Prove2me | solution 1 for Catalog.NumberTheory.QuantTuran.four_mul_sum_min
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:47:50.332823+00:00
-- url     : https://prove2.me/submissions/5a34c013-08ac-43bc-83e0-fe8821ca64d3

import Mathlib
import Definitions.Def_NumberTheory_QuantL1TuranBridge
theorem solution (q : ℕ) : 4 * ∑ j ∈ Finset.range q, min j (q - j) + q % 2 = q ^ 2 := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    match q, ih with
    | 0, _ => simp
    | 1, _ => simp
    | q + 2, ih =>
      have h := ih q (by omega)
      -- peeling the two end terms shifts every other term up by one
      have hstep : ∑ j ∈ Finset.range (q + 2), min j (q + 2 - j)
          = ∑ j ∈ Finset.range q, min j (q - j) + q + 1 := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        have hshift : ∑ j ∈ Finset.range q, min (j + 1) (q + 2 - (j + 1))
            = ∑ j ∈ Finset.range q, (min j (q - j) + 1) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.mem_range] at hj
          rw [show q + 2 - (j + 1) = (q - j) + 1 by omega, min_add_add_right]
        rw [hshift, Finset.sum_add_distrib]
        simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
        omega
      rw [hstep]
      have hsq : (q + 2) ^ 2 = q ^ 2 + 4 * q + 4 := by ring
      omega
