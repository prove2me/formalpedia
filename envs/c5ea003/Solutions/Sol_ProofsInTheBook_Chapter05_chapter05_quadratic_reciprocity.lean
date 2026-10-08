-- Prove2me | solution 1 for ProofsInTheBook.Chapter05.chapter05_quadratic_reciprocity
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T14:43:30.549879+00:00
-- url     : https://prove2.me/submissions/613fd80b-7c55-46cd-bba7-6592b5f95525

import Mathlib


/-!
# Chapter 5: The law of quadratic reciprocity

From "Proofs from THE BOOK":

**Quadratic reciprocity**: For distinct odd primes p and q,
  (q/p) · (p/q) = (-1)^{(p-1)/2 · (q-1)/2}

The book presents Eisenstein's proof via counting lattice points:
the number of lattice points in {1,...,(p-1)/2} × {1,...,(q-1)/2}
below y = (q/p)x equals ∑_{j=1}^{(p-1)/2} ⌊jq/p⌋, which by
Gauss's lemma determines (q/p). Since gcd(p,q) = 1, no point lies
on the diagonal, and the two triangles tile the rectangle of size
(p-1)/2 · (q-1)/2, giving the sign.
-/

namespace ProofsInTheBook.Chapter05

/-!
### Quadratic reciprocity

We state the law using the Legendre symbol `legendreSym`.
-/









end ProofsInTheBook.Chapter05

open ProofsInTheBook.Chapter05

theorem solution (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) :=
  legendreSym.quadratic_reciprocity hp hq hpq
