-- Prove2me | solution 1 for mme_child_grading_implies_parent_grading
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:44:36.294012+00:00
-- url     : https://prove2.me/submissions/44ec049e-f48f-4f0c-b681-fd62a668b3b3

import Definitions.Def_mme_recursive_profiled_CW_data

open BigOperators MME MME.ProfiledCW MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

/-- Complementary child grades recover the fixed grade of each parent position. -/
theorem solution
    {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a : Address half R parent n) (f : Position n → CompleteWord ell)
    (hf : Graded htotal i a f) (r : Fin R) (t : Fin (n r)) :
    (∑ h : Fin 2, ∑ q, (f ⟨r,t,h⟩ q).val) = parent r i := by
  rw [Fin.sum_univ_two, hf, hf]
  simp only [fullCell, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  change ((a r t).val i).val + (parent r i - ((a r t).val i).val) = parent r i
  exact Nat.add_sub_of_le ((a r t).property.2 i)

/-- Source inclusion is needed only on the unbroken words entering the hole count.
Changing the source there preserves the selected count, repair exponent and output. -/
private theorem mme_exact_step_source_refinement_on_unbroken
    {ell N : ℕ} {P Q : Predicate N} (E : ExactStep ell N P)
    (hPQ : ∀ j i f, f ∈ unbrokenWords E.stage.total i (E.address j) (E.stage.mu i) →
      P i (flatten E.stage.positions E.length f) →
      Q i (flatten E.stage.positions E.length f)) :
    ∃ F : ExactStep ell N Q, F.count = E.count ∧
      F.stage.repairExponent = E.stage.repairExponent ∧
      F.copies = E.copies ∧ F.output = E.output := by
  classical
  let F : ExactStep ell N Q := {
    hash := E.hash
    stage := E.stage
    level := E.level
    length := E.length
    count := E.count
    state := E.state
    address := E.address
    injective := E.injective
    target := E.target
    bucketed := E.bucketed
    hashed := E.hashed
    isolated := E.isolated
    holes := by
      intro j i
      apply le_trans _ (E.holes j i)
      apply Nat.mul_le_mul_left
      apply Finset.card_le_card
      apply Finset.union_subset_union
      · intro f hf
        obtain ⟨hf, hnot⟩ := Finset.mem_filter.mp hf
        exact Finset.mem_filter.mpr ⟨hf, fun hp => hnot (hPQ j i f hf hp)⟩
      · exact Finset.Subset.refl _ }
  exact ⟨F,rfl,rfl,rfl,rfl⟩

/-- Exact parent grading can be added to an extraction source without losing copies. -/
private theorem mme_exact_step_source_add_parent_grading
    {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P) :
    ∃ F : ExactStep ell N (fun i x => P i x ∧
      ∀ (r : Fin E.hash.R) (t : Fin (E.hash.n r)),
        (∑ h : Fin 2, ∑ q,
          ((split E.stage.positions E.length x) ⟨r,t,h⟩ q).val) = E.hash.parent r i),
      F.count = E.count ∧ F.stage.repairExponent = E.stage.repairExponent ∧
      F.copies = E.copies ∧ F.output = E.output := by
  apply mme_exact_step_source_refinement_on_unbroken E
  intro j i f hf hp
  refine ⟨hp, ?_⟩
  have hg : Graded E.stage.total i (E.address j) f := (Finset.mem_filter.mp hf).2.1
  intro r t
  have h := solution E.stage.total i (E.address j) f hg r t
  have hsplit : split E.stage.positions E.length
      (flatten E.stage.positions E.length f) = f := by
    funext p q
    simp [split, flatten]
  simpa only [hsplit] using h


#print axioms solution
