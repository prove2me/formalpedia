-- Prove2me | solution 1 for Round10.freeWitness_dvd_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:47:22.479805+00:00
-- url     : https://prove2.me/submissions/7da52cda-d2d7-4c56-872c-388cc0414d1d

-- Sol generated from Geometry/Round10Closures/TraceLemma.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
import Theorems.Thm_Round10_freeWitness_eq
/-
Round-10 Closures — Part I: the trace lemma for free witnesses.

The "free witness" of exponent `k` attached to a semiprime `N = p * q` is the
number of `k`-th roots of unity in `(ZMod N)ˣ`.  The folklore formula

    R_k(N) = gcd(k, p-1) * gcd(k, q-1)

is the arithmetic content of the *trace lemma*: every numeric witness of this
family factors through the pair of gcd-residue coordinates
`(gcd(k,p-1), gcd(k,q-1))`, and through nothing else.

This file gives a complete, sorry-free proof of that formula, together with the
structural lemmas it rests on (root counting in cyclic groups, transport along
group isomorphisms, multiplicativity over direct products, CRT for `ZMod`).
-/

open Round10

open scoped Classical

/-! ## Counting roots of unity -/






/-! ## The unit group of a semiprime modulus -/



/-! ## The free-witness family -/







open Round10 in
theorem solution(p q k : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : Nat.Coprime p q) :
    freeWitness (p * q) k ∣ k ^ 2 := by
  rw [freeWitness_eq p q k hpq, sq]
  exact Nat.mul_dvd_mul (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
