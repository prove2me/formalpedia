-- Prove2me | Theorems.Thm_gpy_fiber_card_eq_pi_card
-- name    : gpy_fiber_card_eq_pi_card
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T20:25:52.109112+00:00
-- url     : https://prove2.me/theorems/9f51297d-9151-4ecd-ab8e-3fc031f5017d
-- title:
--   The fiber over (D, E) is in bijection with local choices
-- statement:
--   For squarefree D, E with D at most R and E at most R, the number of support pairs with products D and E, good at i, and combined modulus lcm D E equals the number of choices of one local choice per prime divisor of lcm D E. Formalization Note: support, goodness, and the local choice finsets are written out in Mathlib terms, with no local definitions.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_fiber_card_eq_pi_card {k : ℕ} {h : Fin k → ℕ} {R : ℕ} {i : Fin k}
    {D E : ℕ} (hsqD : Squarefree D) (hsqE : Squarefree E)
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
      = ((Nat.lcm D E).primeFactors.pi
          (fun p => (Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter
            (fun ab => (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
              (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
                (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
              (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card  := by sorry
