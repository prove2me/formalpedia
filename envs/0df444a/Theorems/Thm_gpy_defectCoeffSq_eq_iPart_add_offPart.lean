-- Prove2me | Theorems.Thm_gpy_defectCoeffSq_eq_iPart_add_offPart
-- name    : gpy_defectCoeffSq_eq_iPart_add_offPart
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T03:07:29.179143+00:00
-- url     : https://prove2.me/theorems/83a38bfd-2bc2-4ab0-ab75-102ea2b30ed5
-- title:
--   The squarefree defect splits into i-part and off-part
-- statement:
--   The squarefree-restricted defect sum splits exactly into its squarefree i-part and squarefree off-part, by the same case split on the i-coordinate modulus. Exact identity. Formalization Note: all sums and gates are written out in Mathlib terms.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_defectCoeffSq_eq_iPart_add_offPart {k : ℕ}
    (h : Fin k → ℕ) (R : ℕ) (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧
              Nat.lcm (d i) (e i) ≠ 1
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0))
      + (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
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
         else 0)) := by sorry
