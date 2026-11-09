-- Prove2me | solution 1 for Couret.CayleyDoublet.distinct_relative_shifts_no_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:47:45.846585+00:00
-- url     : https://prove2.me/submissions/36d0f524-fd4c-46ea-98b3-36f74d9e0ef1

import Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1
import Mathlib
import Theorems.Thm_Couret_CayleyDoublet_relativeOffset_iff
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









/-- A different relative iterate at even one target quotient vertex
rules out any simultaneous conjugacy of both intrinsically coloured arcs. -/
theorem noTwoColourConjugacy {Q R : Type*}
    (g : Q ≃ R)
    (markedQ singleQ : Q → Q)
    (markedR singleR : R → R)
    (hMarked : ∀ x, g (markedQ x) = markedR (g x))
    (hSingle : ∀ x, g (singleQ x) = singleR (g x))
    (k : Nat)
    (hSource : ∀ x : Q, markedQ x = iterateMap singleQ k x)
    (y : R)
    (hNot : markedR y ≠ iterateMap singleR k y) : False := by
  exact hNot ((relativeOffset_iff g markedQ singleQ markedR singleR
    hMarked hSingle k).mp hSource y)


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

/-- Iterating a pure translation is exactly natural-number scaling. -/
theorem iterateMap_add_shift (a : Q) (k : Nat) (x : Q) :
    iterateMap (fun z : Q => z + a) k x = x + k • a := by
  induction k with
  | zero => simp [iterateMap]
  | succ k ih =>
      simp only [iterateMap, ih, succ_nsmul]
      abel

/-- A pair of coloured translations is not simultaneously conjugate
when the source relative offset differs from the target offset. -/
theorem p2m_local_distinct_relative_shifts_no_conjugacy
    (g : Q ≃ R) (a b : Q) (a' b' : R) (k : Nat)
    (hSource : b = k • a) (hTarget : b' ≠ k • a')
    (hP : ∀ x, g (x + b) = g x + b')
    (hQ : ∀ x, g (x + a) = g x + a') : False := by
  have hMark : ∀ x : Q,
      x + b = iterateMap (fun z : Q => z + a) k x := by
    intro x
    rw [iterateMap_add_shift, hSource]
  have hMismatch :
      (0 : R) + b' ≠ iterateMap (fun z : R => z + a') k (0 : R) := by
    simpa [iterateMap_add_shift] using hTarget
  exact noTwoColourConjugacy g
    (fun z : Q => z + b) (fun z : Q => z + a)
    (fun z : R => z + b') (fun z : R => z + a')
    hP hQ k hMark (0 : R) hMismatch


end TwoShiftObstruction
end Couret.CayleyDoublet

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {Q : Type p2m_u_0} {R : Type p2m_u_1} [inst : AddCommGroup.{p2m_u_0} Q] [inst_1 : AddCommGroup.{p2m_u_1} R]
  (g : Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} Q R) (a b : Q) (a' b' : R) (k : Nat),
  @Eq.{p2m_u_0 + 1} Q b
      (@HSMul.hSMul.{0, p2m_u_0, p2m_u_0} Nat Q Q
        (@instHSMul.{0, p2m_u_0} Nat Q
          (@AddMonoid.toNSMul.{p2m_u_0} Q
            (@SubNegMonoid.toAddMonoid.{p2m_u_0} Q
              (@AddGroup.toSubNegMonoid.{p2m_u_0} Q (@AddCommGroup.toAddGroup.{p2m_u_0} Q inst)))))
        k a) →
    @Ne.{p2m_u_1 + 1} R b'
        (@HSMul.hSMul.{0, p2m_u_1, p2m_u_1} Nat R R
          (@instHSMul.{0, p2m_u_1} Nat R
            (@AddMonoid.toNSMul.{p2m_u_1} R
              (@SubNegMonoid.toAddMonoid.{p2m_u_1} R
                (@AddGroup.toSubNegMonoid.{p2m_u_1} R (@AddCommGroup.toAddGroup.{p2m_u_1} R inst_1)))))
          k a') →
      (∀ (x : Q),
          @Eq.{p2m_u_1 + 1} R
            (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
              (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} Q R) Q (fun x => R)
              (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} Q R) Q R (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_1 + 1} Q R))
              g
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} Q Q Q
                (@instHAdd.{p2m_u_0} Q
                  (@AddCommMagma.toAdd.{p2m_u_0} Q
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} Q
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} Q
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} Q inst)))))
                x b))
            (@HAdd.hAdd.{p2m_u_1, p2m_u_1, p2m_u_1} R R R
              (@instHAdd.{p2m_u_1} R
                (@AddCommMagma.toAdd.{p2m_u_1} R
                  (@AddCommSemigroup.toAddCommMagma.{p2m_u_1} R
                    (@AddCommMonoid.toAddCommSemigroup.{p2m_u_1} R
                      (@AddCommGroup.toAddCommMonoid.{p2m_u_1} R inst_1)))))
              (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} Q R) Q (fun x => R)
                (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                  (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} Q R) Q R (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_1 + 1} Q R))
                g x)
              b')) →
        (∀ (x : Q),
            @Eq.{p2m_u_1 + 1} R
              (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} Q R) Q (fun x => R)
                (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                  (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} Q R) Q R (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_1 + 1} Q R))
                g
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} Q Q Q
                  (@instHAdd.{p2m_u_0} Q
                    (@AddCommMagma.toAdd.{p2m_u_0} Q
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} Q
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} Q
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} Q inst)))))
                  x a))
              (@HAdd.hAdd.{p2m_u_1, p2m_u_1, p2m_u_1} R R R
                (@instHAdd.{p2m_u_1} R
                  (@AddCommMagma.toAdd.{p2m_u_1} R
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_1} R
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_1} R
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_1} R inst_1)))))
                (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                  (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} Q R) Q (fun x => R)
                  (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                    (Equiv.{p2m_u_0 + 1, p2m_u_1 + 1} Q R) Q R (@Equiv.instEquivLike.{p2m_u_0 + 1, p2m_u_1 + 1} Q R))
                  g x)
                a')) →
          False := @_root_.Couret.CayleyDoublet.p2m_local_distinct_relative_shifts_no_conjugacy

