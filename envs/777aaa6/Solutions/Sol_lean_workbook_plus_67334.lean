-- Prove2me | solution 1 for lean_workbook_plus_67334
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:59:40.65736+00:00
-- url     : https://prove2.me/submissions/c2c759e7-9393-43a5-9b07-d65871ed2eb0

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

private lemma order_classification {G : Type*} [Group G] (x : G)
    (h2 : x ^ 2 ≠ 1) (h6 : x ^ 6 = 1) : orderOf x = 3 ∨ orderOf x = 6 := by
  have hd : orderOf x ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have hn : ¬ orderOf x ∣ 2 := by
    simpa only [orderOf_dvd_iff_pow_eq_one] using h2
  have hle : orderOf x ≤ 6 := orderOf_le_of_pow_eq_one (by decide) h6
  interval_cases h : orderOf x <;> norm_num [h] at *

theorem solution {G : Type*} [Group G] (x : G) (hx : x ^ 2 ≠ 1)
    (hx1 : x ^ 6 = 1) : x ^ 4 ≠ 1 ∧ x ^ 5 ≠ 1 := by
  constructor
  · intro h4
    have hd := orderOf_dvd_of_pow_eq_one h4
    rcases order_classification x hx hx1 with h | h <;> norm_num [h] at hd
  · intro h5
    have hd := orderOf_dvd_of_pow_eq_one h5
    rcases order_classification x hx hx1 with h | h <;> norm_num [h] at hd
