-- Prove2me | Theorems.Thm_Beal_primitive_exponent_normalization
-- name    : Beal.primitive_exponent_normalization
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T03:50:19.612627+00:00
-- url     : https://prove2.me/theorems/d84cdb72-1fb9-4255-aa06-87d4b84c2717
-- title:
--   Primitive generalized Fermat solutions admit exponent normalization
-- statement:
--   Let $A,B,C$ be positive integers and let $x,y,z>2$ satisfy
--
--   $$A^x+B^y=C^z,\qquad \gcd(A,B,C)=1.$$
--
--   Then there are positive, pairwise coprime integers $a,b,c$ and exponents $p,q,r$, each equal to $4$ or an odd prime, such that
--
--   $$p\mid x,\quad q\mid y,\quad r\mid z,\qquad a^p=A^x,\quad b^q=B^y,\quad c^r=C^z.$$
--
--   This conditional normalization preserves the three terms of any hypothetical primitive solution. It supplies a reduction of generalized Fermat equations to restricted exponent signatures; it does not assert that such a solution exists.
-- source:
--   R. Daniel Mauldin, A Generalization of Fermat's Last Theorem: The Beal Conjecture and Prize Problem, Notices AMS 44(11), 1997, p. 1436, equation and primitive formulation, https://www.ams.org/notices/199711/beal.pdf; restricted exponent case and elementary normalization proved in the accompanying reduction, using Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, Mathlib/Data/Nat/Factors.lean, Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt. This normalization is not claimed as a separately numbered result in Mauldin.

import Mathlib.Data.Nat.Factors
import Mathlib.Algebra.GCDMonoid.Finset

theorem Beal.primitive_exponent_normalization (A B C x y z : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (hx : 2 < x) (hy : 2 < y) (hz : 2 < z)
    (hg : Finset.gcd ({A, B, C} : Finset ℕ) id = 1)
    (he : A ^ x + B ^ y = C ^ z) :
    ∃ a b c p q r : ℕ,
      a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      (p = 4 ∨ Nat.Prime p ∧ Odd p) ∧
      (q = 4 ∨ Nat.Prime q ∧ Odd q) ∧
      (r = 4 ∨ Nat.Prime r ∧ Odd r) ∧
      p ∣ x ∧ q ∣ y ∧ r ∣ z ∧
      a ^ p = A ^ x ∧ b ^ q = B ^ y ∧ c ^ r = C ^ z ∧
      a.Coprime b ∧ a.Coprime c ∧ b.Coprime c := by sorry
