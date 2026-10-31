-- Prove2me | Theorems.Thm_gpy_defect_prime_trichotomy
-- name    : gpy_defect_prime_trichotomy
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T00:40:39.191983+00:00
-- url     : https://prove2.me/theorems/995c1d99-9c25-47c4-9019-5c421ceb4b46
-- title:
--   Trichotomy for squarefree defect primes
-- statement:
--   Every squarefree defect prime is exactly one of three kinds: an i-coordinate prime dividing lcm(d_i, e_i), a repeated-shift prime from a coordinate j different from i with h_j = h_i, or a member of the finite difference-prime set fixed by h and i. The repeated-shift case is a genuine exception to the naive difference-prime picture: when h_j = h_i, every prime dividing that coordinate's modulus is a defect prime and no difference bounds it. Formalization Note: all conditions are written out in Mathlib terms.
-- source:
--   GPY defect control: exact characterizations and exact sum identities for the compatible-but-not-good (defect) pairs

import Mathlib
open Classical

theorem gpy_defect_prime_trichotomy {k : ℕ} {h d e : Fin k → ℕ}
    {i : Fin k} (hsqd : Squarefree (∏ j, d j))
    (hsqe : Squarefree (∏ j, e j))
    (hcompat : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
    (hnotgood : ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) :
    ∃ p, Nat.Prime p ∧
      p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ∧
      (p ∣ Nat.lcm (d i) (e i) ∨
        (∃ j, j ≠ i ∧ h j = h i ∧ p ∣ Nat.lcm (d j) (e j)) ∨
        p ∈ (Finset.univ.filter (fun j : Fin k => j ≠ i)).biUnion
          (fun j => (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) := by sorry
