-- Prove2me | solution 1 for lean_workbook_plus_20042
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:06:38.171529+00:00
-- url     : https://prove2.me/submissions/c661e6ee-6dc7-4571-9aa9-4a5481ae4f07

import Mathlib.Order.OrderIsoNat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

theorem solution (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hab : ∀ n, (a n) ^ 2 ≥ 2 * a n * a (n + 2)) : False := by
  have hstep (n : ℕ) : a (n + 2) < a n := by
    have hmul : a n * (2 * a (n + 2)) ≤ a n * a n := by
      simpa only [pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hab n
    have hle := Nat.le_of_mul_le_mul_left hmul (ha n)
    have hpos := ha (n + 2)
    omega
  apply not_strictAnti_of_wellFoundedLT (fun n : ℕ => a (2 * n))
  apply strictAnti_nat_of_succ_lt
  intro n
  simpa only [Nat.mul_add, Nat.mul_one] using hstep (2 * n)

theorem centered_ratio_bound (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hab : ∀ n, 2 * a n * a (n + 2) ≤ a (n + 1) ^ 2) :
    ∀ n, 2 ^ n * a (n + 1) ≤ a 1 * a n := by
  intro n
  induction n with
  | zero =>
      simpa using Nat.mul_le_mul_left (a 1) (show 1 ≤ a 0 from ha 0)
  | succ n ih =>
      apply Nat.le_of_mul_le_mul_left (c := a n) _ (ha n)
      calc
        a n * (2 ^ (n + 1) * a (n + 1 + 1)) =
            2 ^ n * (2 * a n * a (n + 2)) := by rw [pow_succ]; ring
        _ ≤ 2 ^ n * a (n + 1) ^ 2 := Nat.mul_le_mul_left (2 ^ n) (hab n)
        _ = (2 ^ n * a (n + 1)) * a (n + 1) := by ring
        _ ≤ (a 1 * a n) * a (n + 1) := Nat.mul_le_mul_right (a (n + 1)) ih
        _ = a n * (a 1 * a (n + 1)) := by ring

theorem source_centered_statement (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hab : ∀ n, a (n + 1) ^ 2 ≥ 2 * a n * a (n + 2)) : False := by
  have hstep (n : ℕ) (hn : a 1 ≤ n) : a (n + 1) < a n := by
    have hpow : a 1 < 2 ^ n := lt_of_le_of_lt hn Nat.lt_two_pow_self
    have hbound := centered_ratio_bound a ha hab n
    by_contra h
    have hrev : a n ≤ a (n + 1) := Nat.le_of_not_gt h
    have hmul : 2 ^ n * a (n + 1) ≤ a 1 * a (n + 1) :=
      hbound.trans (Nat.mul_le_mul_left (a 1) hrev)
    have hle := Nat.le_of_mul_le_mul_right hmul (ha (n + 1))
    omega
  apply not_strictAnti_of_wellFoundedLT (fun n : ℕ => a (a 1 + n))
  apply strictAnti_nat_of_succ_lt
  intro n
  simpa only [Nat.add_assoc] using hstep (a 1 + n) (Nat.le_add_right _ _)

theorem source_positive_indexed_statement (a : ℕ → ℕ)
    (ha : ∀ n, 0 < n → 0 < a n)
    (hab : ∀ n, 0 < n → a (n + 1) ^ 2 ≥ 2 * a n * a (n + 2)) : False := by
  apply source_centered_statement (fun n => a (n + 1))
  · intro n
    exact ha (n + 1) (Nat.zero_lt_succ n)
  · intro n
    simpa only [Nat.add_assoc] using hab (n + 1) (Nat.zero_lt_succ n)

#print axioms solution
#print axioms centered_ratio_bound
#print axioms source_centered_statement
#print axioms source_positive_indexed_statement
