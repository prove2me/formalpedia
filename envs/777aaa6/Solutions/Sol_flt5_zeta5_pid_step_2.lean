-- Prove2me | solution 2 for flt5_zeta5_pid_step
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-12T16:05:20.463622+00:00
-- url     : https://prove2.me/submissions/f272d112-b680-415c-a8aa-f98cb219b44d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
import Theorems.Thm_flt5_zeta5_pure_descent

theorem solution (a b c r s c1 : ℤ) (h_eq : a ^ 5 + b ^ 5 = c ^ 5)
    (h_cop : Int.gcd a b = 1) (h5c : (5 : ℤ) ∣ c) (hc : c ≠ 0) (hc1 : c = 5 * c1)
    (hw : a + b = 5 ^ 4 * r ^ 5)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5)
    (hcop_rs : Int.gcd r s = 1) (hrs : r * s = c1) :
    ∃ p q : ℤ, p ^ 5 + q ^ 5 = c1 ^ 5 ∧ Int.gcd p q = 1 ∧
    p.natAbs < c.natAbs ∧ q.natAbs < c.natAbs ∧ p ≠ 0 ∧ q ≠ 0 := by
  -- Z[ζ_5] pure descent: get (p,q) bounded by c1 (not yet by c)
  obtain ⟨p, q, h_pq, h_cop_pq, hp_le, hq_le, hp_ne, hq_ne⟩ :=
    flt5_zeta5_pure_descent a b c r s c1 h_eq h_cop h5c hc hc1 hw hPhi hcop_rs hrs
  -- c1 ≠ 0 (since c = 5*c1, c ≠ 0)
  have hc1_ne : c1 ≠ 0 := by
    intro h; rw [h, mul_zero] at hc1; exact hc hc1
  -- |c1| < |c| (since |c| = 5*|c1| > |c1| when c1 ≠ 0)
  have hsize_c1 : c1.natAbs < c.natAbs := by
    rw [hc1, Int.natAbs_mul]
    have h5 : (5 : ℤ).natAbs = 5 := by norm_num
    rw [h5]
    have h2 := Int.natAbs_pos.mpr hc1_ne
    omega
  -- Combine: |p| ≤ |c1| < |c|, similarly for q
  exact ⟨p, q, h_pq, h_cop_pq,
         Nat.lt_of_le_of_lt hp_le hsize_c1,
         Nat.lt_of_le_of_lt hq_le hsize_c1,
         hp_ne, hq_ne⟩
