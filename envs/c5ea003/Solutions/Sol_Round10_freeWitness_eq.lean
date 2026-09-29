-- Prove2me | solution 1 for Round10.freeWitness_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:45:10.110157+00:00
-- url     : https://prove2.me/submissions/359f9e99-73dc-4813-a87a-51c0bb644d8e

-- Sol generated from Geometry/Round10Closures/TraceLemma.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
import Theorems.Thm_Round10_card_units_zmod_prime
import Theorems.Thm_Round10_rootCount_congr
import Theorems.Thm_Round10_rootCount_of_isCyclic
import Theorems.Thm_Round10_rootCount_prod
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
    freeWitness (p * q) k = (p - 1).gcd k * (q - 1).gcd k := by
  have h1 : freeWitness (p * q) k = rootCount ((ZMod p)ˣ × (ZMod q)ˣ) k :=
    rootCount_congr (unitsMulEquivProd hpq) k
  rw [h1, rootCount_prod, rootCount_of_isCyclic, rootCount_of_isCyclic,
    card_units_zmod_prime, card_units_zmod_prime]
