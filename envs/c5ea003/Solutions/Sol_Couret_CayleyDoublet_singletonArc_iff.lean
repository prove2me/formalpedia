-- Prove2me | solution 1 for Couret.CayleyDoublet.singletonArc_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:44:10.877203+00:00
-- url     : https://prove2.me/submissions/7c507fb7-cadb-43a1-b079-3814f8b15c9c

import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_uniqueMate_natural
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



/-- The other edge colour is also invariant under directed isomorphisms. -/
theorem p2m_local_singletonArc_iff
    (f : V ≃ W) (E : V → V → Prop) (F : W → W → Prop)
    (hE : ∀ x y, E x y ↔ F (f x) (f y))
    (mateV : V → V) (mateW : W → W)
    (hMateV : ∀ x, IsMate E x (mateV x))
    (hUniqueW : ∀ x y, IsMate F x y → y = mateW x)
    (x y : V) :
    SingletonArc E mateV x y ↔ SingletonArc F mateW (f x) (f y) := by
  have hm : f (mateV x) = mateW (f x) :=
    uniqueMate_natural f E F hE mateV mateW hMateV hUniqueW x
  constructor
  · rintro ⟨hxy, hn⟩
    refine ⟨(hE x y).mp hxy, ?_⟩
    intro hh
    have hh' : F (f (mateV x)) (f y) := by
      rw [hm]
      exact hh
    exact hn ((hE (mateV x) y).mpr hh')
  · rintro ⟨hxy, hn⟩
    refine ⟨(hE x y).mpr hxy, ?_⟩
    intro hh
    have hh' : F (f (mateV x)) (f y) :=
      (hE (mateV x) y).mp hh
    rw [hm] at hh'
    exact hn hh'








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

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {V : Type p2m_u_0} {W : Type p2m_u_1} (f : Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} V W) (E : V → V → Prop)
  (F : W → W → Prop),
  (∀ (x y : V),
      Iff (E x y)
        (F
          (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
            (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} V W) V (fun x => W)
            (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
              (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} V W) V W (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_1 + 1} V W))
            f x)
          (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
            (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} V W) V (fun x => W)
            (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
              (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} V W) V W (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_1 + 1} V W))
            f y))) →
    ∀ (mateV : V → V) (mateW : W → W),
      (∀ (x : V), @Couret.CayleyDoublet.IsMate.{p2m_u_0} V E x (mateV x)) →
        (∀ (x y : W), @Couret.CayleyDoublet.IsMate.{p2m_u_1} W F x y → @Eq.{p2m_u_1 + 1} W y (mateW x)) →
          ∀ (x y : V),
            Iff (@Couret.CayleyDoublet.SingletonArc.{p2m_u_0} V E mateV x y)
              (@Couret.CayleyDoublet.SingletonArc.{p2m_u_1} W F mateW
                (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                  (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} V W) V (fun x => W)
                  (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                    (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} V W) V W (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_1 + 1} V W))
                  f x)
                (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                  (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} V W) V (fun x => W)
                  (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                    (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} V W) V W (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_1 + 1} V W))
                  f y)) := @_root_.Couret.CayleyDoublet.p2m_local_singletonArc_iff

