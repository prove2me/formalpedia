-- Prove2me | solution 1 for Round10.card_units_zmod_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:41:20.440677+00:00
-- url     : https://prove2.me/submissions/9d8f1967-cfc0-4c39-9974-2ab4d9d72611

-- Sol generated from Geometry/Round10Closures/TraceLemma.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
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
theorem solution(p : ℕ) [Fact p.Prime] : Nat.card (ZMod p)ˣ = p - 1 := by
  simp [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime (Fact.out : p.Prime)]
