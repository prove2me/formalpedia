-- Prove2me | solution 1 for flt5_zeta5_pure_descent
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T15:50:35.20349+00:00
-- url     : https://prove2.me/submissions/eda9726a-d4a6-409d-a077-03216a75885e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theorems.Thm_flt5_zeta5_ring_witnesses
import Theorems.Thm_flt5_pow5_sum_natAbs_bound

-- Sketch: flt5_zeta5_pure_descent
-- Decomposition:
--   Child 1 (hard, Z[ζ_5] PID step): flt5_zeta5_ring_witnesses
--     Given all descent hypotheses, produces p,q with p^5+q^5=c1^5,
--     gcd(p,q)=1, p≠0, q≠0, and 0 < p*q (same-sign, from ring of integers structure).
--   Child 2 (elementary, integer arithmetic): flt5_pow5_sum_natAbs_bound
--     Given p^5+q^5=c1^5 with p≠0, q≠0, 0<p*q, proves p.natAbs≤c1.natAbs ∧ q.natAbs≤c1.natAbs.

theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧
    p.natAbs ≤ c1.natAbs ∧ q.natAbs ≤ c1.natAbs ∧ p ≠ 0 ∧ q ≠ 0 := by
  -- Step 1: Get witnesses from the Z[ζ_5] PID argument.
  -- flt5_zeta5_ring_witnesses provides p,q with:
  --   p^5+q^5=c1^5, gcd(p,q)=1, p≠0, q≠0, and 0 < p*q.
  -- The same-sign condition 0<p*q comes from the fact that in Z[ζ_5] the witnesses
  -- are norms of conjugate elements, which are positive integers (or both negative).
  obtain ⟨p, q, h_pq, h_gcd, hp_ne, hq_ne, hpq_pos⟩ :=
    flt5_zeta5_ring_witnesses a b c r s c1 h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs
  -- Step 2: Derive the natAbs bounds from the elementary lemma.
  -- flt5_pow5_sum_natAbs_bound: p^5+q^5=c1^5 ∧ p≠0 ∧ q≠0 ∧ 0<p*q → |p|≤|c1| ∧ |q|≤|c1|
  obtain ⟨hp_bound, hq_bound⟩ :=
    flt5_pow5_sum_natAbs_bound p q c1 h_pq hp_ne hq_ne hpq_pos
  exact ⟨p, q, h_pq, h_gcd, hp_bound, hq_bound, hp_ne, hq_ne⟩

