-- Prove2me | solution 1 for ActivationStoneDual.feasible_card_eq_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T16:42:19.707957+00:00
-- url     : https://prove2.me/submissions/9d0c6171-4f0a-44bb-82d9-b445e8968aa0

-- Sol generated from Novelty/ActivationStoneDual.lean
import Mathlib
import Definitions.Def_Novelty_ActivationStoneDual

/-!
# A finite Stone model for neural activation patterns

This file isolates the rigorous finite theorem behind the proposed Stone-duality
picture.  A network with `k` Boolean gates has an activation map
`a : X → (Fin k → Bool)`.  Its feasible Stone space is the range of `a`, not in
general the whole Boolean cube.  Hence it has at most `2^k` points, with equality
exactly when every activation pattern is feasible.

Classifiers constant on activation fibres factor uniquely through this finite
space.  Subsets of the feasible space form a Boolean algebra; their pullbacks are
exactly activation-invariant decision regions.  Finally, the full powerset concept
class on this space has VC dimension equal to its number of points.  This last
statement concerns the *full algebra of regions*, not a single fixed classifier.
-/

open Function Set
open scoped BigOperators

open ActivationStoneDual




/-
The feasible-pattern projection is onto.
-/

/-
There are exactly `2^k` formal activation patterns.
-/

/-
The finite Stone space has at most `2^k` points.
-/

/-
The commonly claimed `2^k` count is valid precisely under feasibility of
all formal activation patterns.
-/



/-
Descending and then projecting recovers the original classifier.
-/

/-
The descended classifier is unique.
-/


/-
Realization preserves complements: Boolean negation of syntax becomes
complement of the geometric decision region.
-/

/-
Realization preserves intersections.
-/

/-
Realization is injective because every feasible pattern has an input witness.
-/

/-
Every activation-invariant binary decision region is the realization of a
unique subset of feasible patterns.
-/


/-
The full Boolean algebra of subsets shatters every set.
-/

/-
Consequently, on a finite Stone space the full clopen/powerset concept class
has VC dimension exactly the number of Stone points (expressed as the sharp
cardinality bound on shattered finite sets).
-/

/-
A single fixed decision region cannot shatter any nonempty set.  Thus VC
dimension belongs to a *family* of classifiers; assigning it to one fixed network
without specifying a parameterized hypothesis class is a category error.
-/



/-
Thus atoms of the feasible-region algebra correspond bijectively to feasible
activation patterns.
-/

/-
The number of atoms therefore equals the number of feasible patterns, and is
at most `2^k` for a `k`-gate network.
-/


open ActivationStoneDual in
theorem solution{X : Type*} [Fintype X] {k : ℕ}
    (a : X → Pattern k) :
    Fintype.card (Feasible a) = 2 ^ k ↔ Function.Surjective a := by
  constructor;
  · intro h
    have h_card : Fintype.card (Feasible a) = Fintype.card (Set.range a) := by
      congr!;
    have h_range : Set.range a = Set.univ := by
      exact Set.eq_of_subset_of_card_le ( Set.subset_univ _ ) ( by aesop );
    exact Set.range_eq_univ.mp h_range;
  · intro ha
    have h_card : Fintype.card (Set.range a) = 2 ^ k := by
      simp +decide [ ha.range_eq ];
    convert h_card
