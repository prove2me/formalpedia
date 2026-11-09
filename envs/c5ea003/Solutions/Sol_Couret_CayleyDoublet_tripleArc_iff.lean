-- Prove2me | solution 1 for Couret.CayleyDoublet.tripleArc_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:32:20.176442+00:00
-- url     : https://prove2.me/submissions/6c150c98-61f8-4312-8fe0-55123c17b05a

import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1
import Mathlib
import Mathlib

set_option autoImplicit false

/-!
CAYLEY-DOUBLET-CORE (13 October 2026).

These kernel-checkable transport lemmas show that a pair of vertices having
at least two distinct common out-neighbors is intrinsically preserved by
any digraph isomorphism. If every vertex admits a unique *other* vertex
with this property, the mate map and the resulting marked quotient arcs
are natural under isomorphisms.

The hypotheses asserting the existence/uniqueness of mates for a specific
Cayley graph are NOT proved by these abstract lemmas. The arithmetic
specialization and cycle-count obstruction remain separate obligations.
No custom proof assumptions, novel priority or universal square-fibre claim.
-/

namespace Couret.CayleyDoublet

variable {V W : Type*}


















end Couret.CayleyDoublet


/-!
CAYLEY-DOUBLET-QUOTIENT-PERIOD (13 October 2026).

Abstract quotient-period transport, building on the compiled intrinsic-mate
and marked-arc lemmas above. A quotient projection and its deterministic
marked successor are EXPLICIT INPUTS. This does not assume or claim that
a specific cyclic Cayley graph satisfies the quotient hypotheses.

The arithmetic specialization S = {a,b,b+m}, the exceptional order-four
degeneracy, and the gcd cycle counts remain independent obligations.
-/

namespace Couret.CayleyDoublet














end Couret.CayleyDoublet

/-!
CAYLEY-DOUBLET-ARITHMETIC (13 October 2026).

The finite cyclic uniqueness criterion is treated separately: the
necessary difference-rigidity hypothesis is explicit here. This file
does NOT identify that hypothesis with the modular arithmetic condition
for every exceptional support. The common-successor quotient projection
and its translation permutation are formalised below.
-/

namespace Couret.CayleyDoublet

section Arithmetic

variable {G : Type*} [AddCommGroup G]













/-- Unfold the three generators without losing their additive structure. -/
theorem p2m_local_tripleArc_iff
    [DecidableEq G] (a b h x y : G) :
    CayleyArc (TripleSupport a b h) x y ↔
      y = x + a ∨ y = x + b ∨ y = x + (b + h) := by
  unfold CayleyArc TripleSupport
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨s, hs, heq⟩
    rcases hs with hs | hs | hs
    · subst s
      exact Or.inl heq
    · subst s
      exact Or.inr (Or.inl heq)
    · subst s
      exact Or.inr (Or.inr heq)
  · intro hy
    rcases hy with ha | hb | hc
    · exact ⟨a, Or.inl rfl, ha⟩
    · exact ⟨b, Or.inr (Or.inl rfl), hb⟩
    · exact ⟨b + h, Or.inr (Or.inr rfl), hc⟩







end Arithmetic

section ShiftOnQuotient

variable {Q : Type*} [AddCommGroup Q]









end ShiftOnQuotient


end Couret.CayleyDoublet


/-!
CAYLEY-DOUBLET-TWO-COLOUR (13 October 2026).

The successor shared by x and its intrinsic mate and the unique successor
not shared by that mate provide two different marked relations. The
second marked relation is transported by graph isomorphisms just as the
first one is. On induced quotients, the relative iterate of the shared
successor with respect to the nonshared successor is an isomorphism
invariant. Here quotient projections, successor existence and uniqueness
remain explicit hypotheses. No cyclic arithmetic has been imported.
-/

namespace Couret.CayleyDoublet

variable {V W : Type*}












end Couret.CayleyDoublet


/-!
CAYLEY-DOUBLET-SINGLETON-SPECIALIZATION (14 October 2026).

These concrete group-level lemmas identify the intrinsic *nonshared*
successor x+a of the triple support {a,b,b+h}, without assuming
DifferenceRigid. Together with markedArc_quotient_formula they show
the two quotient colours are the translations +a and +b, respectively.

The remaining universal obligation is to derive DifferenceRigid from
the exceptional order-three arithmetic in ZMod (2*m). A claim that the
whole infinite-family theorem is Lean-assembled would be premature.
-/

namespace Couret.CayleyDoublet

section SingletonSpecialization

variable {G : Type*} [AddCommGroup G] [DecidableEq G]












end SingletonSpecialization
end Couret.CayleyDoublet


/-!
CAYLEY-ORDER-THREE-BRIDGE (14 October 2026).

Suppose h has order dividing two and a difference d is nonzero
modulo the subgroup {0,h}, with 3*d equal to 0 or h.
Then the extra order-four collision 2*d ∈ {0,h} is impossible.

This is the arithmetic no-degeneracy lemma needed by the
six-difference classification for {a,b,b+h}. It is NOT YET
the complete proof of DifferenceRigid for that Finset.
-/

namespace Couret.CayleyDoublet

section OrderThreeBridge

variable {G : Type*} [AddCommGroup G]






end OrderThreeBridge
end Couret.CayleyDoublet


/-!
CAYLEY-ORDER-THREE-SIGNED-DIFFERENCES (14 October 2026).
The four cross differences of {a,b,b+h}, written as
d, d+h, -d, -d+h (where d=a-b), are pairwise distinct
whenever d is nontrivial modulo {0,h} and 3*d = 0 or h.
This is a reusable group-level piece of DifferenceRigid.
-/
namespace Couret.CayleyDoublet

section SignedCrossDifferences

variable {G : Type*} [AddCommGroup G]




end SignedCrossDifferences
end Couret.CayleyDoublet


/-!
CAYLEY-TRIPLE-RIGIDITY (14 October 2026).
Enumerate all ordered differences of {a,b,b+h}; under exceptional
order-three arithmetic the only repeated nonzero difference is h.
This is a finite exhaustive symbolic case proof, kernel checked by Lean.
-/
namespace Couret.CayleyDoublet
section ExceptionalTripleRigidity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]






end ExceptionalTripleRigidity
end Couret.CayleyDoublet


/-!
CAYLEY-TWO-COLOUR-ARITHMETIC-ASSEMBLY (14 October 2026).

This section completes two reusable links:
(1) instantiate the proved exceptional rigid triple with both intrinsic
    quotient colours +a and +b in any additive quotient killing h;
(2) show that two such shift colours cannot be simultaneously conjugate
    if the first marked step is a k-th unshared step in the source
    but not in the target.

The existence of a concrete induced quotient equivalence for an
arbitrary digraph isomorphism, and ZMod (12*r) arithmetic for every r,
are still separate formalization obligations.
-/

namespace Couret.CayleyDoublet

section ExceptionalTwoColourPackage

variable {G Q : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup Q]




end ExceptionalTwoColourPackage

section TwoShiftObstruction

variable {Q R : Type*} [AddCommGroup Q] [AddCommGroup R]






end TwoShiftObstruction
end Couret.CayleyDoublet

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (a b h x y : G),
  Iff
    (@Couret.CayleyDoublet.CayleyArc.{p2m_u_0} G inst
      (@Couret.CayleyDoublet.TripleSupport.{p2m_u_0} G inst inst_1 a b h) x y)
    (Or
      (@Eq.{p2m_u_0 + 1} G y
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          x a))
      (Or
        (@Eq.{p2m_u_0 + 1} G y
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            x b))
        (@Eq.{p2m_u_0 + 1} G y
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            x
            (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHAdd.{p2m_u_0} G
                (@AddCommMagma.toAdd.{p2m_u_0} G
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
              b h))))) := @_root_.Couret.CayleyDoublet.p2m_local_tripleArc_iff

