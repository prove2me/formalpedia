-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_canonical_counter_equal_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:08.829999+00:00
-- url     : https://prove2.me/submissions/0d33a4bd-83de-4c3a-b485-3f1adf72da58

import Aesop
import Definitions.Def_Couret_RecohCanonicalRepresentations_728d443f1366
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohTypedObservation_b23b2e33136b
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a

set_option autoImplicit false

/-!
Canonical numeric points and ordered counters for the Python v0.2 boundary.

A typed point has one natural coordinate strictly below each nonzero modulus.
The maps below construct the correspondence with the product of `ZMod`s;
no interpretation hypothesis is supplied by a caller.  The arithmetic is the
modular arithmetic used by `_add`, `_sub`, and `_double`.  The list counter
counts all ordered pairs, including the diagonal and repeated resulting sums.

This module does not model Python objects, tuple sorting, JSON parsing,
exceptions, or execution of the Python interpreter.  In particular, the
no-duplicate hypothesis on a support is essential when a list is replaced by
a finite set.
-/

namespace Couret.STROBO2TORS

section Coordinates

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]







theorem recoh_point_decode_encode (x : RecohCanonicalPoint q) :
    recohPointDecode q (recohPointEncode q x) = x := by
  funext i
  apply Fin.ext
  simp [recohPointDecode, recohPointEncode, ZMod.val_natCast,
    Nat.mod_eq_of_lt (x i).isLt]

theorem recoh_point_encode_decode (x : (i : Fin d) → ZMod (q i)) :
    recohPointEncode q (recohPointDecode q x) = x := by
  funext i
  exact ZMod.natCast_zmod_val (x i)

theorem recoh_point_encode_injective : Function.Injective (recohPointEncode q) := by
  intro x y h
  have h' := congrArg (recohPointDecode q) h
  simpa only [recoh_point_decode_encode] using h'









theorem recoh_point_encode_add (x y : RecohCanonicalPoint q) :
    recohPointEncode q (recohPointAdd q x y) =
      recohPointEncode q x + recohPointEncode q y := by
  funext i
  simp [recohPointEncode, recohPointAdd]













end Coordinates

section ListCounters

variable {G : Type*} [AddCommGroup G] [DecidableEq G]





omit [AddCommGroup G] in
private theorem recoh_count_map_sum {α : Type*} (xs : List α) (f : α → G) (z : G) :
    (xs.map f).count z = (xs.map (fun x => if f x = z then 1 else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : f x = z
    · simp [h, ih, Nat.add_comm]
    · simp [h, ih]

theorem recoh_list_pair_sums_count (xs ys : List G) (z : G) :
    (recohListPairSums xs ys).count z =
      (xs.map (fun x => (ys.map (fun y => if x + y = z then 1 else 0)).sum)).sum := by
  induction xs with
  | nil => simp [recohListPairSums]
  | cons x xs ih =>
    simpa only [recohListPairSums, List.flatMap_cons, List.count_append,
      List.map_cons, List.sum_cons, recoh_count_map_sum] using
      congrArg (fun n => (ys.map (fun y => if x + y = z then 1 else 0)).sum + n) ih

private theorem recoh_sum_map_to_finset {α β : Type*} [DecidableEq α]
    [AddCommMonoid β] (xs : List α) (hxs : xs.Nodup) (f : α → β) :
    (xs.map f).sum = xs.toFinset.sum f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, htail⟩ := List.nodup_cons.mp hxs
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using hx), ih htail]

/-- A duplicate-free list counter is exactly the finite-support convolution
square, with no assumption on the surrounding group's cardinality. -/
theorem recoh_list_counter_eq_ordered_square (xs : List G) (hxs : xs.Nodup) (z : G) :
    recohListCounter xs z = orderedSquare xs.toFinset z := by
  unfold recohListCounter
  rw [recoh_list_pair_sums_count]
  simp_rw [recoh_sum_map_to_finset xs hxs]
  rfl











end ListCounters

section CanonicalCounters

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





theorem recoh_canonical_pair_sums_encode
    (xs ys : List (RecohCanonicalPoint q)) :
    (recohCanonicalPairSums q xs ys).map (recohPointEncode q) =
      recohListPairSums (xs.map (recohPointEncode q)) (ys.map (recohPointEncode q)) := by
  simp only [recohCanonicalPairSums, recohListPairSums, List.map_flatMap,
    List.flatMap_map, List.map_map, Function.comp_def, recoh_point_encode_add]

private theorem recoh_count_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) (z : α) :
    (xs.map f).count (f z) = xs.count z := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : x = z
    · simp [h, ih]
    · have h' : f x ≠ f z := fun e => h (hf e)
      simp [h, h', ih]

/-- Counts computed on canonical tuples agree with counts in the cyclic
product because encoding preserves addition and never identifies points. -/
theorem recoh_canonical_counter_eq_list_counter
    (xs : List (RecohCanonicalPoint q)) (z : RecohCanonicalPoint q) :
    recohCanonicalCounter q xs z =
      recohListCounter (xs.map (recohPointEncode q)) (recohPointEncode q z) := by
  unfold recohCanonicalCounter recohListCounter
  rw [← recoh_canonical_pair_sums_encode]
  exact (recoh_count_map_injective (recohPointEncode q)
    (recoh_point_encode_injective q) _ z).symm

/-- Concrete coordinate-counter bridge to the established Lean square. -/
theorem recoh_canonical_counter_eq_ordered_square
    (xs : List (RecohCanonicalPoint q)) (hxs : xs.Nodup)
    (z : RecohCanonicalPoint q) :
    recohCanonicalCounter q xs z =
      orderedSquare (xs.map (recohPointEncode q)).toFinset (recohPointEncode q z) := by
  rw [recoh_canonical_counter_eq_list_counter]
  exact recoh_list_counter_eq_ordered_square _
    (List.Nodup.map (recoh_point_encode_injective q) hxs) _

/-- Equality of canonical point-counter functions loses no information
relative to equality of the labelled squares in the cyclic product. -/
theorem p2m_local_recoh_canonical_counter_equal_iff
    (xs ys : List (RecohCanonicalPoint q)) (hxs : xs.Nodup) (hys : ys.Nodup) :
    recohCanonicalCounter q xs = recohCanonicalCounter q ys ↔
      orderedSquare (xs.map (recohPointEncode q)).toFinset =
        orderedSquare (ys.map (recohPointEncode q)).toFinset := by
  constructor
  · intro h
    funext z
    have hz := congrFun h (recohPointDecode q z)
    rw [recoh_canonical_counter_eq_ordered_square q xs hxs,
      recoh_canonical_counter_eq_ordered_square q ys hys,
      recoh_point_encode_decode] at hz
    exact hz
  · intro h
    funext z
    rw [recoh_canonical_counter_eq_ordered_square q xs hxs,
      recoh_canonical_counter_eq_ordered_square q ys hys]
    exact congrFun h (recohPointEncode q z)

end CanonicalCounters

end Couret.STROBO2TORS

theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (xs ys : List.{0} (@Couret.STROBO2TORS.RecohCanonicalPoint d q)),
  @List.Nodup.{0} (@Couret.STROBO2TORS.RecohCanonicalPoint d q) xs →
    @List.Nodup.{0} (@Couret.STROBO2TORS.RecohCanonicalPoint d q) ys →
      Iff
        (@Eq.{1} (@Couret.STROBO2TORS.RecohCanonicalPoint d q → Nat)
          (@Couret.STROBO2TORS.recohCanonicalCounter d q inst xs)
          (@Couret.STROBO2TORS.recohCanonicalCounter d q inst ys))
        (@Eq.{1} (((i : Fin d) → ZMod (q i)) → Nat)
          (@Couret.STROBO2TORS.orderedSquare.{0} ((i : Fin d) → ZMod (q i))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            (@List.toFinset.{0} ((i : Fin d) → ZMod (q i))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              (@List.map.{0, 0} (@Couret.STROBO2TORS.RecohCanonicalPoint d q) ((i : Fin d) → ZMod (q i))
                (@Couret.STROBO2TORS.recohPointEncode d q) xs)))
          (@Couret.STROBO2TORS.orderedSquare.{0} ((i : Fin d) → ZMod (q i))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            (@List.toFinset.{0} ((i : Fin d) → ZMod (q i))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              (@List.map.{0, 0} (@Couret.STROBO2TORS.RecohCanonicalPoint d q) ((i : Fin d) → ZMod (q i))
                (@Couret.STROBO2TORS.recohPointEncode d q) ys)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_canonical_counter_equal_iff

