-- Prove2me | Theorems.Thm_gpy_goodPair_noncong
-- name    : gpy_goodPair_noncong
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T21:03:46.006055+00:00
-- url     : https://prove2.me/theorems/0d5b1bd1-9b69-44ee-a7aa-a61966f09ab8
-- title:
--   A good pair has no congruent-shift prime
-- statement:
--   A pair good at a coordinate i never has a prime p dividing some coordinate modulus lcm(d_j, e_j) with h_i congruent to h_j modulo p: the witness satisfies p dividing w + h_j, the congruence gives p dividing w + h_i, and p dividing the combined modulus, contradicting coprimality. Formalization Note: goodness is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_goodPair_noncong {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    {p : ℕ} (hp : Nat.Prime p)
    (hg : ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) {j : Fin k}
    (hj : p ∣ Nat.lcm (d j) (e j)) : ¬ h i ≡ h j [MOD p] := by sorry
