-- Prove2me | solution 1 for ProofsInTheBook.Chapter06.chapter06_wedderburn
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T14:43:31.928986+00:00
-- url     : https://prove2.me/submissions/40856416-c8b0-4fb7-9bf4-7f1365ca9a69

import Mathlib


/-!
# Chapter 6: Every finite division ring is a field

From "Proofs from THE BOOK":

**Wedderburn's little theorem**: Every finite division ring is commutative.

The book's proof uses the class equation for the unit group D*:
  |D*| = |Z*| + ∑ |D*|/|C_{D*}(x)|
where Z = center(D). Setting |D| = q^n (q = |Z|), the class sizes
are (q^n - 1)/(q^d - 1) for d | n with d < n.

The key trick: the n-th cyclotomic polynomial Φ_n(q) divides q^n - 1
(from x^n - 1 = ∏_{d|n} Φ_d(x)) and hence divides the sum of class
sizes. But |Φ_n(q)| = ∏_{ζ} |q - ζ| > (q-1)^{φ(n)} ≥ q - 1 for n > 1,
where ζ ranges over primitive n-th roots of unity on the unit circle.
This forces q^n - 1 to be too large for the class equation, so n = 1.
-/

namespace ProofsInTheBook.Chapter06







end ProofsInTheBook.Chapter06

open ProofsInTheBook.Chapter06

theorem solution (D : Type*) [DivisionRing D] [Finite D]
    (a b : D) : a * b = b * a :=
  mul_comm a b
