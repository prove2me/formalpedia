-- Prove2me | solution 1 for AnalyticCombinatorics.Ch2.SetPartitions.expected_blocks_eq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T11:16:25.321984+00:00
-- url     : https://prove2.me/submissions/a7e874fa-0a1a-4186-ad6b-32fe8408e389

import Definitions.Def_AnalyticCombinatorics_Ch2_SetPartitions_BellMean
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Bell numbers as finite set partitions

This file uses `Finpartition (Finset.univ : Finset (Fin n))` as the type of genuine
set partitions of `[n]`.
-/

namespace AnalyticCombinatorics.Ch2.SetPartitions

open Finset Function

noncomputable section

-- The equivalences below transport `Finpartition`s through finset/subtype complements;
-- the larger heartbeat budget is for those local `simp`/`grind` calls.
set_option maxHeartbeats 400000

private lemma bellNumber_univ_card (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (Finpartition (Finset.univ : Finset α)) =
      bellNumber (Fintype.card α) := by
  unfold bellNumber
  exact Fintype.card_congr (finpartitionUnivCongr (Fintype.equivFin α))

private lemma card_fiber_eq_sum {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) :
    Fintype.card α = ∑ b : β, Fintype.card {a : α // f a = b} := by
  calc
    Fintype.card α = Fintype.card (Σ b : β, {a : α // f a = b}) := by
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ = ∑ b : β, Fintype.card {a : α // f a = b} := by
      rw [Fintype.card_sigma]

private lemma subtype_notMem_card {α : Type*} [Fintype α] [DecidableEq α] (B : Finset α) :
    Fintype.card {x : α // x ∉ B} = Fintype.card α - B.card := by
  rw [Fintype.card_subtype]
  have hset : ({x | x ∉ B} : Finset α) = (Finset.univ : Finset α) \ B := by
    ext x
    simp
  rw [hset, Finset.card_sdiff_of_subset (by simp), Finset.card_univ]

/-- Counts partitions by the block containing a distinguished root. -/
private lemma bellNumber_root_sum (α : Type*) [Fintype α] [DecidableEq α] (r : α) :
    Fintype.card (Finpartition (Finset.univ : Finset α)) =
      ∑ B : {B : Finset α // r ∈ B},
        Fintype.card (Finpartition (Finset.univ : Finset {x : α // x ∉ B.val})) := by
  classical
  let block : Finpartition (Finset.univ : Finset α) → {B : Finset α // r ∈ B} :=
    fun P => ⟨P.part r, by simpa using P.mem_part (by simp)⟩
  rw [card_fiber_eq_sum block]
  refine Finset.sum_congr rfl fun B _ => ?_
  let fiberEquiv :
      {P : Finpartition (Finset.univ : Finset α) // block P = B} ≃
        {P : Finpartition (Finset.univ : Finset α) // P.part r = B.val} :=
    { toFun := fun P => ⟨P.val, by
        have h := congrArg Subtype.val P.property
        exact h⟩
      invFun := fun P => ⟨P.val, by
        apply Subtype.ext
        exact P.property⟩
      left_inv := by
        intro P
        apply Subtype.ext
        rfl
      right_inv := by
        intro P
        apply Subtype.ext
        rfl }
  let rootEquiv := finpartitionRootFiberEquiv r B.property
  calc
    Fintype.card {P : Finpartition (Finset.univ : Finset α) // block P = B}
        = Fintype.card {P : Finpartition (Finset.univ : Finset α) // P.part r = B.val} := by
          exact Fintype.card_congr fiberEquiv
    _ = Fintype.card (Finpartition ((Finset.univ : Finset α) \ B.val)) := by
          exact Fintype.card_congr rootEquiv
    _ = Fintype.card (Finpartition (Finset.univ : Finset {x : α // x ∉ B.val})) := by
          exact Fintype.card_congr (finpartitionSdiffSubtypeCongr B.val)

@[simp] private lemma rootBlockEquiv_card (n : ℕ) (S : Finset (Fin n)) :
    (rootBlockEquiv n S).val.card = S.card + 1 := by
  simp [rootBlockEquiv]

private lemma rootBlockEquiv_compl_card (n : ℕ) (S : Finset (Fin n)) :
    Fintype.card {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val} = n - S.card := by
  rw [subtype_notMem_card, Fintype.card_fin, rootBlockEquiv_card]
  omega

private lemma bellNumber_succ_eq_sum_subsets (n : ℕ) :
    bellNumber (n + 1) = ∑ S : Finset (Fin n), bellNumber (n - S.card) := by
  classical
  unfold bellNumber
  rw [bellNumber_root_sum (Fin (n + 1)) (Fin.last n)]
  symm
  exact Fintype.sum_equiv (rootBlockEquiv n)
    (fun S : Finset (Fin n) => bellNumber (n - S.card))
    (fun B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B} =>
      Fintype.card (Finpartition (Finset.univ : Finset {x : Fin (n + 1) // x ∉ B.val})))
    (by
      intro S
      change bellNumber (n - S.card) =
        Fintype.card
          (Finpartition
            (Finset.univ : Finset {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val}))
      rw [bellNumber_univ_card, rootBlockEquiv_compl_card])

private lemma markedBlock_fiber_card (n : ℕ)
    (A : {A : Finset (Fin n) // A.Nonempty}) :
    Fintype.card {x : MarkedBlock n // markedBlockMap n x = A} =
      bellNumber (n - A.val.card) := by
  classical
  let a : Fin n := A.property.choose
  have ha : a ∈ A.val := A.property.choose_spec
  let e₁ := markedBlockFiberEquiv n A
  let e₂ := finpartitionRootFiberEquiv a ha
  calc
    Fintype.card {x : MarkedBlock n // markedBlockMap n x = A}
        = Fintype.card
            {P : Finpartition (Finset.univ : Finset (Fin n)) // P.part a = A.val} := by
          exact Fintype.card_congr e₁
    _ = Fintype.card (Finpartition ((Finset.univ : Finset (Fin n)) \ A.val)) := by
          exact Fintype.card_congr e₂
    _ = Fintype.card (Finpartition (Finset.univ : Finset {x : Fin n // x ∉ A.val})) := by
          exact Fintype.card_congr (finpartitionSdiffSubtypeCongr A.val)
    _ = bellNumber (n - A.val.card) := by
          rw [bellNumber_univ_card, subtype_notMem_card, Fintype.card_fin]

private lemma sum_parts_eq_nonempty_subsets (n : ℕ) :
    (∑ P : Finpartition (Finset.univ : Finset (Fin n)), P.parts.card) =
      ∑ A : {A : Finset (Fin n) // A.Nonempty}, bellNumber (n - A.val.card) := by
  classical
  calc
    (∑ P : Finpartition (Finset.univ : Finset (Fin n)), P.parts.card)
        = Fintype.card (MarkedBlock n) := by
          rw [Fintype.card_sigma]
          refine Finset.sum_congr rfl fun P _ => ?_
          simp
    _ = ∑ A : {A : Finset (Fin n) // A.Nonempty},
          Fintype.card {x : MarkedBlock n // markedBlockMap n x = A} := by
          exact card_fiber_eq_sum (markedBlockMap n)
    _ = ∑ A : {A : Finset (Fin n) // A.Nonempty}, bellNumber (n - A.val.card) := by
          refine Finset.sum_congr rfl fun A _ => markedBlock_fiber_card n A

private lemma sum_finsets_empty_or_nonempty {α : Type*} [Fintype α] [DecidableEq α]
    (f : Finset α → ℕ) :
    (∑ S : Finset α, f S) =
      f ∅ + ∑ A : {S : Finset α // S.Nonempty}, f A.val := by
  classical
  let e : Finset α ≃ Option {S : Finset α // S.Nonempty} :=
    { toFun := fun S => if h : S.Nonempty then some ⟨S, h⟩ else none
      invFun := fun o => match o with
        | none => ∅
        | some S => S.val
      left_inv := by
        intro S
        by_cases h : S.Nonempty
        · simp [h]
        · simp [h, Finset.not_nonempty_iff_eq_empty.mp h]
      right_inv := by
        intro o
        cases o with
        | none => simp
        | some S => simp [S.property] }
  calc
    (∑ S : Finset α, f S)
        = ∑ o : Option {S : Finset α // S.Nonempty},
            match o with
            | none => f ∅
            | some S => f S.val := by
          exact Fintype.sum_equiv e
            f
            (fun o : Option {S : Finset α // S.Nonempty} =>
              match o with
              | none => f ∅
              | some S => f S.val)
            (by
              intro S
              by_cases h : S.Nonempty
              · simp [e, h]
              · simp [e, h, Finset.not_nonempty_iff_eq_empty.mp h])
    _ = f ∅ + ∑ A : {S : Finset α // S.Nonempty}, f A.val := by
          simp

/-- Addition form of the exact first moment identity. -/
theorem bellNumber_succ_eq_sum_parts_add (n : ℕ) :
    bellNumber (n + 1) =
      (∑ P : Finpartition (Finset.univ : Finset (Fin n)), P.parts.card) + bellNumber n := by
  classical
  rw [bellNumber_succ_eq_sum_subsets]
  rw [sum_finsets_empty_or_nonempty (α := Fin n) (fun S => bellNumber (n - S.card))]
  rw [sum_parts_eq_nonempty_subsets]
  simp [add_comm]

end
end AnalyticCombinatorics.Ch2.SetPartitions

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.SetPartitions
open Finset Function
set_option maxHeartbeats 400000
theorem solution (n : ℕ) (hB : 0 < bellNumber n) :
    (∑ P : Finpartition (Finset.univ : Finset (Fin n)), (P.parts.card : ℚ)) / bellNumber n
      = bellNumber (n + 1) / bellNumber n - 1 := by
  classical
  let Sℕ : ℕ := ∑ P : Finpartition (Finset.univ : Finset (Fin n)), P.parts.card
  have hNat : bellNumber (n + 1) = Sℕ + bellNumber n := bellNumber_succ_eq_sum_parts_add n
  have hRat : ((Sℕ : ℚ) + (bellNumber n : ℚ)) = (bellNumber (n + 1) : ℚ) := by
    exact_mod_cast hNat.symm
  have hBq : (bellNumber n : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hB)
  have hsumCast :
      (∑ P : Finpartition (Finset.univ : Finset (Fin n)), (P.parts.card : ℚ)) = (Sℕ : ℚ) := by
    simp [Sℕ]
  rw [hsumCast]
  change (Sℕ : ℚ) / (bellNumber n : ℚ) =
    (bellNumber (n + 1) : ℚ) / (bellNumber n : ℚ) - 1
  rw [← hRat]
  field_simp [hBq]
  ring
