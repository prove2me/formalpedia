-- Prove2me | solution 1 for MatroidMinorBridge.finite_forbidden_minor_characterization
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:36:29.555024+00:00
-- url     : https://prove2.me/submissions/7c0b3385-7171-4f57-9fb2-d64fd126d64a

-- Sol generated from Novelty/MatroidMinorFiniteObstructions.lean
import Mathlib
import Definitions.Def_Novelty_MatroidMinorFiniteObstructions
import Mathlib.Order.WellFoundedSet

/-!
# From well-quasi-ordering to finite forbidden-minor descriptions

This file isolates the order-theoretic bridge underlying forbidden-minor theorems.
An object `a` is read as a minor of `b` when `a ≤ b`.  A class `Good` is
minor-closed when it is downward closed.  The theorem proves that a
well-quasi-order forces every such class to have a finite obstruction set.

The result is deliberately abstract: it applies to graphs, matroids, words under
embedding, and other containment orders.  It does not assume the unresolved
well-quasi-ordering statement for finite-field-representable matroids.
-/

open MatroidMinorBridge

variable {α : Type*} [PartialOrder α]


/-- Minimal excluded objects form an antichain. -/
theorem excluded_isAntichain (Good : α → Prop) :
    IsAntichain (· ≤ ·) {x | IsExcluded Good x} := by
  intro x hx y hy hne hle
  exact hx.1 (hy.2 x (lt_of_le_of_ne hle hne))

/-- In a well-founded containment order, every bad object contains a minimal bad object. -/
theorem exists_excluded_below (Good : α → Prop)
    [WellFoundedLT α] {x : α} (hx : ¬ Good x) :
    ∃ e, IsExcluded Good e ∧ e ≤ x := by
  have hwf : WellFounded (α := α) (· < ·) := wellFounded_lt
  exact hwf.fix (C := fun y => ¬Good y → ∃ e, IsExcluded Good e ∧ e ≤ y) 
    (fun y ih => fun hy => by
      by_cases hall : ∀ z < y, Good z
      · exact ⟨y, ⟨hy, hall⟩, le_rfl⟩
      · push_neg at hall
        obtain ⟨z, hzy, hzy_bad⟩ := hall
        obtain ⟨e, he_excl, he_le_z⟩ := ih z hzy hzy_bad
        exact ⟨e, he_excl, le_trans he_le_z (le_of_lt hzy)⟩) x hx



open MatroidMinorBridge in
theorem solution[WellQuasiOrderedLE α]
    (Good : α → Prop)
    (hdown : ∀ ⦃a b : α⦄, a ≤ b → Good b → Good a) :
    ∃ forbidden : Finset α,
      (∀ e ∈ forbidden, IsExcluded Good e) ∧
      ∀ x, Good x ↔ ∀ e ∈ forbidden, ¬ e ≤ x := by
  let S : Set α := {e | IsExcluded Good e}
  have hS : S.Finite := by
    exact WellQuasiOrderedLE.finite_of_isAntichain (excluded_isAntichain Good)
  let forbidden : Finset α := hS.toFinset
  refine ⟨forbidden, ?_, ?_⟩
  · intro e he
    have heS : e ∈ S := by
      simpa [forbidden] using he
    exact heS
  · intro x
    constructor
    · intro hx e he he_le
      have heS : e ∈ S := by
        simpa [forbidden] using he
      exact heS.1 (hdown he_le hx)
    · intro havoid
      by_contra hx
      obtain ⟨e, he, he_le⟩ := exists_excluded_below Good hx
      have he_mem : e ∈ forbidden := by
        simpa [forbidden] using (show e ∈ S from he)
      exact havoid e he_mem he_le
