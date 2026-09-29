-- Prove2me | solution 1 for Round10.rootCount_of_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:42:07.886328+00:00
-- url     : https://prove2.me/submissions/7e1ea51e-f7fd-49cd-93cb-b55d35980cf7

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


/-- The `k`-torsion of a commutative group is the kernel of the `k`-th power map. -/
theorem rootCount_eq_card_ker (G : Type*) [CommGroup G] (k : ℕ) :
    rootCount G k = Nat.card (powMonoidHom k : G →* G).ker :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [MonoidHom.mem_ker, powMonoidHom])




/-! ## The unit group of a semiprime modulus -/



/-! ## The free-witness family -/







open Round10 in
theorem solution(G : Type*) [CommGroup G] [IsCyclic G] [Finite G] (k : ℕ) :
    rootCount G k = (Nat.card G).gcd k := by
  rw [rootCount_eq_card_ker, IsCyclic.card_powMonoidHom_ker]
