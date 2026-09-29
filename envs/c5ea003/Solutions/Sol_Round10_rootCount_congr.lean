-- Prove2me | solution 1 for Round10.rootCount_congr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:41:58.817534+00:00
-- url     : https://prove2.me/submissions/278a880b-68ad-4374-8ea1-e8fcd1eb8802

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
theorem solution{G H : Type*} [Group G] [Group H] (e : G ≃* H) (k : ℕ) :
    rootCount G k = rootCount H k := by
  refine Nat.card_congr ⟨fun x => ⟨e x, by rw [← map_pow, x.2, map_one]⟩,
    fun y => ⟨e.symm y, by rw [← map_pow, y.2, map_one]⟩, ?_, ?_⟩ <;> intro x <;> simp
