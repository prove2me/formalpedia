-- Prove2me | solution 1 for lean_workbook_plus_42602
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:28:48.158307+00:00
-- url     : https://prove2.me/submissions/ce3d8fb4-826a-4f63-8a02-b166faf63750

import Mathlib

namespace FiniteFunctionAgreementCount

theorem unequal_choices {B : Type*} [Fintype B] [DecidableEq B] (b : B) :
    Fintype.card {y : B // b ≠ y} = Fintype.card B - 1 := by
  simp

theorem no_agreement_count {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B) :
    Fintype.card {g : A → B // ∀ x, f x ≠ g x} =
      (Fintype.card B - 1) ^ Fintype.card A := by
  classical
  have he : {g : A → B // ∀ x, f x ≠ g x} ≃
      ((x : A) → {y : B // f x ≠ y}) :=
    Equiv.subtypePiEquivPi (p := fun x y => f x ≠ y)
  rw [Fintype.card_congr he, Fintype.card_pi]
  simp only [unequal_choices, Finset.prod_const, Finset.card_univ]

theorem agreement_count {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B) :
    Fintype.card {g : A → B // ∃ x, f x = g x} =
      Fintype.card B ^ Fintype.card A -
        (Fintype.card B - 1) ^ Fintype.card A := by
  classical
  have h := Fintype.card_subtype_compl (fun g : A → B => ∀ x, f x ≠ g x)
  simpa only [not_forall, not_not, Fintype.card_fun, no_agreement_count] using h

theorem agreement_finset_count {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B) :
    (Finset.univ.filter (fun g : A → B => ∃ x, f x = g x)).card =
      Fintype.card B ^ Fintype.card A -
        (Fintype.card B - 1) ^ Fintype.card A := by
  rw [← Fintype.card_subtype]
  exact agreement_count f

theorem prescribed_choices {A B : Type*} [Fintype B] [DecidableEq A]
    [DecidableEq B] (f : A → B) (s : Finset A) (x : A) :
    Fintype.card {y : B // f x = y ↔ x ∈ s} =
      if x ∈ s then 1 else Fintype.card B - 1 := by
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx]

theorem prescribed_agreement_count {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B) (s : Finset A) :
    Fintype.card {g : A → B // ∀ x, f x = g x ↔ x ∈ s} =
      (Fintype.card B - 1) ^ (Fintype.card A - s.card) := by
  classical
  have he : {g : A → B // ∀ x, f x = g x ↔ x ∈ s} ≃
      ((x : A) → {y : B // f x = y ↔ x ∈ s}) :=
    Equiv.subtypePiEquivPi (p := fun x y => f x = y ↔ x ∈ s)
  rw [Fintype.card_congr he, Fintype.card_pi]
  simp only [prescribed_choices]
  rw [Finset.prod_ite]
  have hc : (Finset.univ.filter (fun x : A => x ∉ s)) = sᶜ := by
    ext x
    simp
  simp [hc, Finset.card_compl]

theorem count_independent_of_reference {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f h : A → B) :
    Fintype.card {g : A → B // ∃ x, f x = g x} =
      Fintype.card {g : A → B // ∃ x, h x = g x} := by
  rw [agreement_count, agreement_count]

theorem source_count (f : Fin 3 → Fin 3) :
    Fintype.card {g : Fin 3 → Fin 3 // ∃ x, f x = g x} = 19 := by
  convert agreement_count f using 1
  congr!

theorem source_no_agreement_count (f : Fin 3 → Fin 3) :
    Fintype.card {g : Fin 3 → Fin 3 // ∀ x, f x ≠ g x} = 8 := by
  convert no_agreement_count f using 1
  congr!

theorem source_finset_count (f : Fin 3 → Fin 3) :
    (Finset.univ.filter (fun g : Fin 3 → Fin 3 => ∃ x, f x = g x)).card = 19 := by
  convert agreement_finset_count f using 1
  congr!

end FiniteFunctionAgreementCount

theorem solution (f : Fin 3 → Fin 3) :
    ∃ g : Fin 3 → Fin 3, ∃ x : Fin 3, f x = g x := by
  have hn : Nonempty {g : Fin 3 → Fin 3 // ∃ x, f x = g x} :=
    Fintype.card_pos_iff.mp (by rw [FiniteFunctionAgreementCount.source_count]; decide)
  obtain ⟨g, hg⟩ := hn
  exact ⟨g, hg⟩
