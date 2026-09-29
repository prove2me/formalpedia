-- Prove2me | solution 3 for flt5_zeta5_pid_step
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T17:37:49.284026+00:00
-- url     : https://prove2.me/submissions/7296f1d3-9c71-48d2-ab83-e3f5faa4eb74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Theorems.Thm_flt5_zeta5_pure_descent

-- Sketch: flt5_zeta5_pid_step
-- Child: flt5_zeta5_pure_descent (gets p,q with |p|,|q|≤|c1|)
-- Upgrades to |p|,|q| < |c| using |c| = 5*|c1| > |c1| when c1 ≠ 0.

theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧
    p.natAbs < c.natAbs ∧ q.natAbs < c.natAbs ∧ p ≠ 0 ∧ q ≠ 0 := by
  obtain ⟨p, q, h_pq, h_cop_pq, hp_le, hq_le, hp_ne, hq_ne⟩ :=
    flt5_zeta5_pure_descent a b c r s c1 h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs
  have hc1_ne : c1 ≠ 0 := by
    intro h
    exact hc (show c = 0 by omega)
  have hsize_c1 : c1.natAbs < c.natAbs := by
    have hpos : 0 < c1.natAbs := Int.natAbs_pos.mpr hc1_ne
    have key : (c1.natAbs : ℤ) < c.natAbs := by
      rcases Int.natAbs_eq c with h1 | h1 <;>
      rcases Int.natAbs_eq c1 with h2 | h2 <;>
      omega
    exact_mod_cast key
  exact ⟨p, q, h_pq, h_cop_pq,
         Nat.lt_of_le_of_lt hp_le hsize_c1,
         Nat.lt_of_le_of_lt hq_le hsize_c1,
         hp_ne, hq_ne⟩
