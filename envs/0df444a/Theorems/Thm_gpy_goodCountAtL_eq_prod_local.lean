-- Prove2me | Theorems.Thm_gpy_goodCountAtL_eq_prod_local
-- name    : gpy_goodCountAtL_eq_prod_local
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T20:28:57.615994+00:00
-- url     : https://prove2.me/theorems/c68e817b-cc7f-492d-ab19-81704b223f9b
-- title:
--   The good-pair count factors as a product of local counts
-- statement:
--   For squarefree D, E with D at most R and E at most R, the good-pair count at modulus lcm D E equals the product over the prime divisors of lcm D E of the local choice counts. No admissibility hypothesis. Formalization Note: the count, support, goodness, and local choice finsets are written out in Mathlib terms, with no local definitions.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_goodCountAtL_eq_prod_local {k : ℕ} {h : Fin k → ℕ} {R : ℕ}
    {i : Fin k} {D E : ℕ} (hsqD : Squarefree D) (hsqE : Squarefree E)
    (hDR : D ≤ R) (hER : E ≤ R) :
    ((((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R) ×ˢ
      (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)).filter
      (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧
        (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E))).card
      = ∏ p ∈ (Nat.lcm D E).primeFactors,
          ((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter
            (fun ab => (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
              (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
                (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
              (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))).card  := by sorry
