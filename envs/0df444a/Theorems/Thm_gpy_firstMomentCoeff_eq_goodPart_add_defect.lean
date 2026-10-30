-- Prove2me | Theorems.Thm_gpy_firstMomentCoeff_eq_goodPart_add_defect
-- name    : gpy_firstMomentCoeff_eq_goodPart_add_defect
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T01:08:47.933185+00:00
-- url     : https://prove2.me/theorems/ee188896-9aa4-40eb-8073-fcb09b5e6800
-- title:
--   Defect decomposition of the first-moment coefficient
-- statement:
--   For a tuple $h$, level $R$, general coefficients $\lambda$, and a coordinate $i$, the first-moment coefficient splits exactly into the good part — the un-rescaled version of the singular-sum terms — plus the defect, the sum over compatible-but-not-good pairs. Together with the rescaled comparison, this is the whole comparison: the ratio analysis must evaluate the good part and control the defect, which is the precise obstruction to reading the singular sum off the first-moment coefficient. Formalization Note: the coefficient, the support set, goodness, and compatibility are all written out in Mathlib terms, with no local definitions.
-- source:
--   GPY first-moment comparison, formalized from Mathlib (compatible pairs, good pairs, and the singular sum)

import Mathlib
open Classical

theorem gpy_firstMomentCoeff_eq_goodPart_add_defect {k : ℕ} (h : Fin k → ℕ)
    (R : ℕ) (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
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
