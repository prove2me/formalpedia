-- Prove2me | Theorems.Thm_gpy_defectOffPartSq_eq_tied_sum
-- name    : gpy_defectOffPartSq_eq_tied_sum
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T03:52:54.9922+00:00
-- url     : https://prove2.me/theorems/225c80e9-a6ea-423f-a0d7-92634856e335
-- title:
--   The squarefree off-part is exactly the tied sum
-- statement:
--   The squarefree off-part equals exactly the sum over compatible (1,1)-slice pairs satisfying the tied difference-or-repeated-shift condition. Exact identity; the support is evaluated, not bounded. Formalization Note: all sums and gates are written out in Mathlib terms.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_defectOffPartSq_eq_tied_sum {k : ℕ} (h : Fin k → ℕ)
    (R : ℕ) (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧
              Nat.lcm (d i) (e i) = 1
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      ∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              Nat.lcm (d i) (e i) = 1 ∧
          (∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
            (h j = h i ∨
              p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) then
          lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0) := by sorry
