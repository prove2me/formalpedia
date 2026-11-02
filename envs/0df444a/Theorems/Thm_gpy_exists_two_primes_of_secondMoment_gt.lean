-- Prove2me | Theorems.Thm_gpy_exists_two_primes_of_secondMoment_gt
-- name    : gpy_exists_two_primes_of_secondMoment_gt
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T08:27:06.964927+00:00
-- url     : https://prove2.me/theorems/113a66fa-234f-4bc3-9188-f21aa56c52f4
-- title:
--   GPY criterion: second moment exceeding first moment forces two primes in one translate
-- statement:
--   If the linear second moment over an interval exceeds the first moment over the same interval, some translate in the interval carries primes at two distinct coordinates. The weight, second moment, and prime indicator are written out in Mathlib terms.
-- source:
--   GPY ratio analysis: threshold, main-term approximations, and BV level cap

import Mathlib
open Classical

theorem gpy_exists_two_primes_of_secondMoment_gt {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (lam : (Fin k → ℕ) → ℝ) {x y : ℕ} (hgt : (∑ n ∈ Finset.Ioc x y, ((∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2)) < (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) * ((∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2))) : ∃ n ∈ Finset.Ioc x y, ∃ i j, i ≠ j ∧ Nat.Prime (n + h i) ∧ Nat.Prime (n + h j) := by sorry
