-- Prove2me | Theorems.Thm_gpy_not_goodPair_of_prime_cong
-- name    : gpy_not_goodPair_of_prime_cong
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T21:16:44.660986+00:00
-- url     : https://prove2.me/theorems/9f4fe9ef-5775-4131-843b-0a98171a4f78
-- title:
--   A congruent-shift prime kills goodness
-- statement:
--   Contrapositive of the previous statement: a prime dividing a coordinate modulus with a congruent shift implies the pair is not good at i. Formalization Note: goodness is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_not_goodPair_of_prime_cong {k : ℕ} {h d e : Fin k → ℕ}
    {i : Fin k} {p : ℕ} (hp : Nat.Prime p) {j : Fin k}
    (hj : p ∣ Nat.lcm (d j) (e j)) (hcong : h i ≡ h j [MOD p]) :
    ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) := by sorry
