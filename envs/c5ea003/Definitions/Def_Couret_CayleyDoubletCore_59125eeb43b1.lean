-- Prove2me | Definitions.Def_Couret_CayleyDoubletCore_59125eeb43b1
-- name    : Couret_CayleyDoubletCore_59125eeb43b1
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:31.987405+00:00
-- url     : https://prove2.me/theorems/6dedf4d3-cdc5-42e7-a8a3-2d33c823f0dd
-- title:
--   Intrinsic mates and coloured Cayley arcs
-- statement:
--   For a directed relation, two-shared means at least two distinct common out-neighbours, and a mate is a distinct vertex with that property. Shared and unshared arcs relative to a mate map define two intrinsic colours. The group specialization uses $$x\to y\iff y-x\in S,\qquad S=\{a,b,b+h\}.$$ The bundle also supplies difference rigidity, quotient translations, and finite iteration maps.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/65b828d9ffd016ce2a1b05403f303fa5f948c10f/research/correspondants_20261013/lean/CayleyDoubletCore.lean; source file SHA-256 7162f949e4d7aece3f9241308253678a1dadd2e7255ff303aab69f6bf9731a4a

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

/-- Two distinct common out-neighbors of x and y. -/
def TwoShared (E : V → V → Prop) (x y : V) : Prop :=
  Exists fun p : V => Exists fun q : V =>
    p ≠ q ∧ E x p ∧ E y p ∧ E x q ∧ E y q





/-- A mate is a distinct vertex having two common out-neighbors. -/
def IsMate (E : V → V → Prop) (x y : V) : Prop :=
  x ≠ y ∧ TwoShared E x y





/-- Marked arcs: an out-neighbor shared with the vertex's intrinsic mate. -/
def DoubletArc (E : V → V → Prop) (mate : V → V) (x y : V) : Prop :=
  E x y ∧ E (mate x) y




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

/-- Iterate an intrinsic quotient successor map exactly n times. -/
def iterateMap {Q : Type*} (P : Q → Q) : Nat → Q → Q
  | 0, x => x
  | n + 1, x => P (iterateMap P n x)












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

/-- Arc x -> x+s for an increment in a finite support. -/
def CayleyArc (S : Finset G) (x y : G) : Prop :=
  ∃ s ∈ S, y = x + s

/-- A repeated nonzero difference from different source increments can
only equal h. This is an explicit, checkable combinatorial hypothesis. -/
def DifferenceRigid (S : Finset G) (h : G) : Prop :=
  ∀ u v u' v' : G,
    u ∈ S → v ∈ S → u' ∈ S → v' ∈ S →
    u ≠ u' → u ≠ v → u - v = u' - v' → u - v = h



/-- The exceptional three-element support, before imposing 3(b-a)=0. -/
def TripleSupport [DecidableEq G] (a b h : G) : Finset G :=
  {a, b, b + h}













end Arithmetic

section ShiftOnQuotient

variable {Q : Type*} [AddCommGroup Q]

/-- Translation by b is an explicit permutation on every additive quotient. -/
def quotientShift (b : Q) : Q ≃ Q where
  toFun x := x + b
  invFun x := x - b
  left_inv x := by simp
  right_inv x := by simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Recursion for successive quotient steps. -/
def shiftSteps (b : Q) : Nat → Q → Q
  | 0, x => x
  | k + 1, x => shiftSteps b k x + b





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

/-- An outgoing arc not shared by the intrinsic mate. -/
def SingletonArc (E : V → V → Prop) (mate : V → V) (x y : V) : Prop :=
  E x y ∧ ¬ E (mate x) y










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


