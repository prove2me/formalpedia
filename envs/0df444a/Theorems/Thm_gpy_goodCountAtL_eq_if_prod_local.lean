-- Prove2me | Theorems.Thm_gpy_goodCountAtL_eq_if_prod_local
-- name    : gpy_goodCountAtL_eq_if_prod_local
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T20:32:02.423092+00:00
-- url     : https://prove2.me/theorems/c2148ba5-804d-436f-ace8-be76518a3eed
-- title:
--   The good-pair count at a general modulus is the product or zero
-- statement:
--   For squarefree D, E with D at most R and E at most R, the good-pair count at a general modulus L equals the product of the local counts over the prime divisors of lcm D E when L equals lcm D E, and 0 otherwise. Formalization Note: the count, support, goodness, and local choice finsets are written out in Mathlib terms, with no local definitions.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_goodCountAtL_eq_if_prod_local {k : ℕ} {h : Fin k → ℕ} {R : ℕ}
    {i : Fin k} {D E L : ℕ} (hsqD : Squarefree D) (hsqE : Squarefree E)
    (hDR : D ≤ R) (hER : E ≤ R) :
    ((((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R) ×ˢ
      (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)).filter
      (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧
        (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L))).card
      = if L = Nat.lcm D E then
          ∏ p ∈ (Nat.lcm D E).primeFactors,
            ((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter
              (fun ab => (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
                (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
                  (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
                (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))).card
        else 0  := by sorry
