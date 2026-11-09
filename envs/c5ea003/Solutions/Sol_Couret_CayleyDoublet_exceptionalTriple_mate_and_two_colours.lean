-- Prove2me | solution 1 for Couret.CayleyDoublet.exceptionalTriple_mate_and_two_colours
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:48:49.513329+00:00
-- url     : https://prove2.me/submissions/854cb834-c3ce-451f-a3a6-1160c2a3e274

import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_halfTurn_unique_of_order_three
import Theorems.Thm_Couret_CayleyDoublet_markedArc_iff_pair
import Theorems.Thm_Couret_CayleyDoublet_singletonArc_iff_point
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



















/-- Any additive quotient that kills h sends both marked successors
to exactly one vertex: pi(x)+pi(b). -/
theorem markedArc_quotient_formula
    [DecidableEq G] {Q : Type*} [AddCommGroup Q]
    (pi : G →+ Q) (a b h : G) (hpi : pi h = 0)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hab : a ≠ b) (habh : a ≠ b + h) (x y : G)
    (harc : DoubletArc (CayleyArc (TripleSupport a b h))
      (fun z => z + h) x y) :
    pi y = pi x + pi b := by
  rcases (markedArc_iff_pair a b h hhalf hne hab habh x y).mp harc with hb | hc
  · simp [hb, map_add]
  · simp [hc, map_add, hpi]

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







/-- Every additive quotient sends the nonshared successor to +pi(a). -/
theorem singletonArc_quotient_formula
    {Q : Type*} [AddCommGroup Q] (pi : G →+ Q)
    (a b h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hab : a ≠ b) (habh : a ≠ b + h)
    (x y : G)
    (harc : SingletonArc (CayleyArc (TripleSupport a b h))
      (fun z => z + h) x y) :
    pi y = pi x + pi a := by
  have hy := (singletonArc_iff_point a b h hhalf hne hab habh x y).mp harc
  simp [hy, map_add]

/-- In the exact same quotient, marked and unshared arcs have distinct
explicit translations. The quotient is not assumed to be cyclic. -/
theorem bothColours_quotient_formulas
    {Q : Type*} [AddCommGroup Q] (pi : G →+ Q)
    (a b h : G) (hpi : pi h = 0)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (hab : a ≠ b) (habh : a ≠ b + h)
    (x y : G) :
    (DoubletArc (CayleyArc (TripleSupport a b h))
      (fun z => z + h) x y →
        pi y = pi x + pi b) ∧
    (SingletonArc (CayleyArc (TripleSupport a b h))
      (fun z => z + h) x y →
        pi y = pi x + pi a) := by
  constructor
  · intro hd
    exact markedArc_quotient_formula pi a b h hpi hhalf hne hab habh x y hd
  · intro hs
    exact singletonArc_quotient_formula pi a b h hhalf hne hab habh x y hs


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

/-- Rigid exceptional support: unique mate plus formulas for both
intrinsic successor colours on any additive quotient killing h. -/
theorem p2m_local_exceptionalTriple_mate_and_two_colours
    (pi : G →+ Q) (a b h : G)
    (hpi : pi h = 0) (hhalf : h + h = 0) (hne : h ≠ 0)
    (hd0 : a - b ≠ 0) (hdh : a - b ≠ h)
    (hthree : (a - b) + (a - b) + (a - b) = 0 ∨
      (a - b) + (a - b) + (a - b) = h)
    (x y : G) :
    (IsMate (CayleyArc (TripleSupport a b h)) x y ↔ y = x + h) ∧
    (DoubletArc (CayleyArc (TripleSupport a b h))
      (fun z => z + h) x y → pi y = pi x + pi b) ∧
    (SingletonArc (CayleyArc (TripleSupport a b h))
      (fun z => z + h) x y → pi y = pi x + pi a) := by
  have hab : a ≠ b := by
    intro he
    apply hd0
    rw [he]
    simp
  have habh : a ≠ b + h := by
    intro he
    apply hdh
    calc
      a - b = (b + h) - b := by rw [he]
      _ = h := by abel
  have hm := halfTurn_unique_of_order_three
    a b h hhalf hne hd0 hdh hthree x y
  have hc := bothColours_quotient_formulas
    pi a b h hpi hhalf hne hab habh x y
  exact ⟨hm, hc.1, hc.2⟩


end ExceptionalTwoColourPackage

section TwoShiftObstruction

variable {Q R : Type*} [AddCommGroup Q] [AddCommGroup R]






end TwoShiftObstruction
end Couret.CayleyDoublet

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} {Q : Type p2m_u_1} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : AddCommGroup.{p2m_u_1} Q]
  (pi :
    @AddMonoidHom.{p2m_u_0, p2m_u_1} G Q
      (@AddZeroClass.toAddZero.{p2m_u_0} G
        (@AddMonoid.toAddZeroClass.{p2m_u_0} G
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
      (@AddZeroClass.toAddZero.{p2m_u_1} Q
        (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
          (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
            (@AddGroup.toSubNegMonoid.{p2m_u_1} Q (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
  (a b h : G),
  @Eq.{p2m_u_1 + 1} Q
      (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
        (@AddMonoidHom.{p2m_u_0, p2m_u_1} G Q
          (@AddZeroClass.toAddZero.{p2m_u_0} G
            (@AddMonoid.toAddZeroClass.{p2m_u_0} G
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
          (@AddZeroClass.toAddZero.{p2m_u_1} Q
            (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
              (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                (@AddGroup.toSubNegMonoid.{p2m_u_1} Q (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
        G (fun x => Q)
        (@AddMonoidHom.instFunLike.{p2m_u_0, p2m_u_1} G Q
          (@AddZeroClass.toAddZero.{p2m_u_0} G
            (@AddMonoid.toAddZeroClass.{p2m_u_0} G
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
          (@AddZeroClass.toAddZero.{p2m_u_1} Q
            (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
              (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                (@AddGroup.toSubNegMonoid.{p2m_u_1} Q (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
        pi h)
      (@OfNat.ofNat.{p2m_u_1} Q (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_1} Q
          (@NegZeroClass.toZero.{p2m_u_1} Q
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_1} Q
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_1} Q
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_1} Q
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_1} Q inst_2))))))) →
    @Eq.{p2m_u_0 + 1} G
        (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          h h)
        (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
          (@Zero.toOfNat0.{p2m_u_0} G
            (@NegZeroClass.toZero.{p2m_u_0} G
              (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                  (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                    (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
      @Ne.{p2m_u_0 + 1} G h
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
        @Ne.{p2m_u_0 + 1} G
            (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
              (@instHSub.{p2m_u_0} G
                (@SubNegMonoid.toSub.{p2m_u_0} G
                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
              a b)
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
          @Ne.{p2m_u_0 + 1} G
              (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHSub.{p2m_u_0} G
                  (@SubNegMonoid.toSub.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                a b)
              h →
            Or
                (@Eq.{p2m_u_0 + 1} G
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a b)
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a b))
                    (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHSub.{p2m_u_0} G
                        (@SubNegMonoid.toSub.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                      a b))
                  (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                    (@Zero.toOfNat0.{p2m_u_0} G
                      (@NegZeroClass.toZero.{p2m_u_0} G
                        (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                          (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                            (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                              (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))))
                (@Eq.{p2m_u_0 + 1} G
                  (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                    (@instHAdd.{p2m_u_0} G
                      (@AddCommMagma.toAdd.{p2m_u_0} G
                        (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                          (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                            (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                    (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHAdd.{p2m_u_0} G
                        (@AddCommMagma.toAdd.{p2m_u_0} G
                          (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                            (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                              (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a b)
                      (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHSub.{p2m_u_0} G
                          (@SubNegMonoid.toSub.{p2m_u_0} G
                            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                        a b))
                    (@HSub.hSub.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                      (@instHSub.{p2m_u_0} G
                        (@SubNegMonoid.toSub.{p2m_u_0} G
                          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))
                      a b))
                  h) →
              ∀ (x y : G),
                And
                  (Iff
                    (@Couret.CayleyDoublet.IsMate.{p2m_u_0} G
                      (@Couret.CayleyDoublet.CayleyArc.{p2m_u_0} G inst
                        (@Couret.CayleyDoublet.TripleSupport.{p2m_u_0} G inst inst_1 a b h))
                      x y)
                    (@Eq.{p2m_u_0 + 1} G y
                      (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                        (@instHAdd.{p2m_u_0} G
                          (@AddCommMagma.toAdd.{p2m_u_0} G
                            (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                              (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                        x h)))
                  (And
                    (@Couret.CayleyDoublet.DoubletArc.{p2m_u_0} G
                        (@Couret.CayleyDoublet.CayleyArc.{p2m_u_0} G inst
                          (@Couret.CayleyDoublet.TripleSupport.{p2m_u_0} G inst inst_1 a b h))
                        (fun z =>
                          @HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            z h)
                        x y →
                      @Eq.{p2m_u_1 + 1} Q
                        (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                          (@AddMonoidHom.{p2m_u_0, p2m_u_1} G Q
                            (@AddZeroClass.toAddZero.{p2m_u_0} G
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                            (@AddZeroClass.toAddZero.{p2m_u_1} Q
                              (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                  (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                    (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                          G (fun x => Q)
                          (@AddMonoidHom.instFunLike.{p2m_u_0, p2m_u_1} G Q
                            (@AddZeroClass.toAddZero.{p2m_u_0} G
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                            (@AddZeroClass.toAddZero.{p2m_u_1} Q
                              (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                  (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                    (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                          pi y)
                        (@HAdd.hAdd.{p2m_u_1, p2m_u_1, p2m_u_1} Q Q Q
                          (@instHAdd.{p2m_u_1} Q
                            (@AddCommMagma.toAdd.{p2m_u_1} Q
                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_1} Q
                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_1} Q
                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_1} Q inst_2)))))
                          (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                            (@AddMonoidHom.{p2m_u_0, p2m_u_1} G Q
                              (@AddZeroClass.toAddZero.{p2m_u_0} G
                                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} Q
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                            G (fun x => Q)
                            (@AddMonoidHom.instFunLike.{p2m_u_0, p2m_u_1} G Q
                              (@AddZeroClass.toAddZero.{p2m_u_0} G
                                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} Q
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                            pi x)
                          (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                            (@AddMonoidHom.{p2m_u_0, p2m_u_1} G Q
                              (@AddZeroClass.toAddZero.{p2m_u_0} G
                                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} Q
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                            G (fun x => Q)
                            (@AddMonoidHom.instFunLike.{p2m_u_0, p2m_u_1} G Q
                              (@AddZeroClass.toAddZero.{p2m_u_0} G
                                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} Q
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                            pi b)))
                    (@Couret.CayleyDoublet.SingletonArc.{p2m_u_0} G
                        (@Couret.CayleyDoublet.CayleyArc.{p2m_u_0} G inst
                          (@Couret.CayleyDoublet.TripleSupport.{p2m_u_0} G inst inst_1 a b h))
                        (fun z =>
                          @HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                            (@instHAdd.{p2m_u_0} G
                              (@AddCommMagma.toAdd.{p2m_u_0} G
                                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                                    (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                            z h)
                        x y →
                      @Eq.{p2m_u_1 + 1} Q
                        (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                          (@AddMonoidHom.{p2m_u_0, p2m_u_1} G Q
                            (@AddZeroClass.toAddZero.{p2m_u_0} G
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                            (@AddZeroClass.toAddZero.{p2m_u_1} Q
                              (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                  (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                    (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                          G (fun x => Q)
                          (@AddMonoidHom.instFunLike.{p2m_u_0, p2m_u_1} G Q
                            (@AddZeroClass.toAddZero.{p2m_u_0} G
                              (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                  (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                            (@AddZeroClass.toAddZero.{p2m_u_1} Q
                              (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                  (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                    (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                          pi y)
                        (@HAdd.hAdd.{p2m_u_1, p2m_u_1, p2m_u_1} Q Q Q
                          (@instHAdd.{p2m_u_1} Q
                            (@AddCommMagma.toAdd.{p2m_u_1} Q
                              (@AddCommSemigroup.toAddCommMagma.{p2m_u_1} Q
                                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_1} Q
                                  (@AddCommGroup.toAddCommMonoid.{p2m_u_1} Q inst_2)))))
                          (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                            (@AddMonoidHom.{p2m_u_0, p2m_u_1} G Q
                              (@AddZeroClass.toAddZero.{p2m_u_0} G
                                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} Q
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                            G (fun x => Q)
                            (@AddMonoidHom.instFunLike.{p2m_u_0, p2m_u_1} G Q
                              (@AddZeroClass.toAddZero.{p2m_u_0} G
                                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} Q
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                            pi x)
                          (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                            (@AddMonoidHom.{p2m_u_0, p2m_u_1} G Q
                              (@AddZeroClass.toAddZero.{p2m_u_0} G
                                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} Q
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                            G (fun x => Q)
                            (@AddMonoidHom.instFunLike.{p2m_u_0, p2m_u_1} G Q
                              (@AddZeroClass.toAddZero.{p2m_u_0} G
                                (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G
                                      (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))))
                              (@AddZeroClass.toAddZero.{p2m_u_1} Q
                                (@AddMonoid.toAddZeroClass.{p2m_u_1} Q
                                  (@SubNegMonoid.toAddMonoid.{p2m_u_1} Q
                                    (@AddGroup.toSubNegMonoid.{p2m_u_1} Q
                                      (@AddCommGroup.toAddGroup.{p2m_u_1} Q inst_2))))))
                            pi a)))) := @_root_.Couret.CayleyDoublet.p2m_local_exceptionalTriple_mate_and_two_colours

