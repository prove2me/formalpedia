-- Prove2me | solution 1 for lean_workbook_plus_60482
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:49:36.828318+00:00
-- url     : https://prove2.me/submissions/5748e0c2-8983-4ed4-b476-c2c36c935da4

import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic

private theorem commuting_preceding_power {G : Type*} [Group G]
    {a b : G} {n : ℕ} (hn : 1 ≤ n) (ha : a ^ n = 1) :
    Commute (a ^ (n - 1)) b ↔ Commute a b := by
  have hmul : a ^ (n - 1) * a = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hn, ha]
  have hinv : a ^ (n - 1) = a⁻¹ := (inv_eq_of_mul_eq_one_left hmul).symm
  rw [hinv, Commute.inv_left_iff]

theorem solution {G : Type*} [Group G] {a b : G} {n : ℕ}
    (h : 1 < n) (h' : a ^ n = 1) (h'' : a ^ (n - 1) * b = b * a ^ (n - 1)) :
    a * b = b * a := by
  exact ((commuting_preceding_power (by omega) h').mp h'').eq
