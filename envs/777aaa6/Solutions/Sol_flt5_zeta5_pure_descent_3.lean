-- Prove2me | solution 3 for flt5_zeta5_pure_descent
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-13T18:33:03.681533+00:00
-- url     : https://prove2.me/submissions/6d80fd50-ecfc-4faf-99cb-2cb69b856e45
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_zeta5_ring_witnesses
import Theorems.Thm_flt5_pow5_sum_natAbs_bound

-- Sketch: flt5_zeta5_pure_descent
-- Decomposes into:
--   Child 1 (hard, Z[zeta_5] PID): flt5_zeta5_ring_witnesses
--     Produces p,q with p^5+q^5=c1^5, gcd(p,q)=1, p,q≠0, 0<p*q
--   Child 2 (elementary): flt5_pow5_sum_natAbs_bound
--     From p^5+q^5=c1^5 with same-sign p,q, derives |p|≤|c1| ∧ |q|≤|c1|

theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧
    p.natAbs ≤ c1.natAbs ∧ q.natAbs ≤ c1.natAbs ∧ p ≠ 0 ∧ q ≠ 0 := by
  obtain ⟨p, q, h_pq, h_gcd, hp_ne, hq_ne, hpq_pos⟩ :=
    flt5_zeta5_ring_witnesses a b c r s c1 h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs
  obtain ⟨hp_bound, hq_bound⟩ :=
    flt5_pow5_sum_natAbs_bound p q c1 h_pq hp_ne hq_ne hpq_pos
  exact ⟨p, q, h_pq, h_gcd, hp_bound, hq_bound, hp_ne, hq_ne⟩
