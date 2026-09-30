-- Prove2me | solution 1 for lean_workbook_plus_49156
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:28:42.803886+00:00
-- url     : https://prove2.me/submissions/b9b902dd-f80d-4e4c-b642-2685bef86cf8

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

private theorem corrected_binomial_identity (n m : ℕ) (h : 2 * m ≤ n) :
    n.choose m * (n - m).choose (n - 2 * m) =
      n.choose (2 * m) * (2 * m).choose m := by
  rw [← Nat.choose_symm (by omega : n - 2 * m ≤ n - m),
    show n - m - (n - 2 * m) = m by omega]
  simpa only [show 2 * m - m = m by omega] using
    (Nat.choose_mul (n := n) (k := 2 * m) (s := m) (by omega)).symm

theorem solution : ¬ (∀ n m : ℕ,
    (n.choose m) * (n - m).choose (n - 2 * m) =
      (n.choose (2 * m)) * (2 * m).choose n) := by
  intro h
  have hc := h 4 1
  norm_num [Nat.choose] at hc
