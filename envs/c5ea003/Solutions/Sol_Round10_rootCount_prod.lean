-- Prove2me | solution 1 for Round10.rootCount_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:42:08.394956+00:00
-- url     : https://prove2.me/submissions/842451ba-7527-464b-9361-4f9d05dbe73c

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
theorem solution(G H : Type*) [Group G] [Group H] (k : ℕ) :
    rootCount (G × H) k = rootCount G k * rootCount H k := by
  rw [rootCount, rootCount, rootCount, ← Nat.card_prod]
  refine Nat.card_congr ⟨fun x => (⟨x.1.1, ?_⟩, ⟨x.1.2, ?_⟩),
    fun y => ⟨(y.1.1, y.2.1), ?_⟩, ?_, ?_⟩
  · have := x.2; rw [Prod.ext_iff] at this; exact this.1
  · have := x.2; rw [Prod.ext_iff] at this; exact this.2
  · rw [Prod.ext_iff]; exact ⟨y.1.2, y.2.2⟩
  · intro x; ext <;> rfl
  · intro y; ext <;> rfl
