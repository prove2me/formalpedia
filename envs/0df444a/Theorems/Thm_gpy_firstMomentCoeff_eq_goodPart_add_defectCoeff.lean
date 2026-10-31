-- Prove2me | Theorems.Thm_gpy_firstMomentCoeff_eq_goodPart_add_defectCoeff
-- name    : gpy_firstMomentCoeff_eq_goodPart_add_defectCoeff
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T02:21:20.665646+00:00
-- url     : https://prove2.me/theorems/23963e05-1dde-4d59-aa5b-9650ac71a9f9
-- title:
--   The first-moment coefficient splits as good part plus defect
-- statement:
--   The first-moment coefficient, the 1/L sum over compatible support pairs, equals exactly the sum over good pairs plus the defect sum over compatible-but-not-good pairs. This is an exact identity, not an estimate. Formalization Note: support, compatibility, and goodness are written out in Mathlib terms.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_firstMomentCoeff_eq_goodPart_add_defectCoeff {k : ℕ}
    (h : Fin k → ℕ) (R : ℕ) (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0))
      + (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then lam d * lam e /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) := by sorry
