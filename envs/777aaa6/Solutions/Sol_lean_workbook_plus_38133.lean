-- Prove2me | solution 1 for lean_workbook_plus_38133
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:38:58.200192+00:00
-- url     : https://prove2.me/submissions/96fab8ff-2232-4404-b6e6-fccb9c80e22d

import Mathlib

noncomputable section

namespace FiniteInvolutionEnumeration

abbrev Inv (A : Type*) := {f : Equiv.Perm A // Function.Involutive f}

def functionEquiv (A : Type*) :
    {f : A → A // Function.Involutive f} ≃ Inv A where
  toFun f := ⟨f.2.toPerm f.1, f.2⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv f := rfl
  right_inv f := by
    apply Subtype.ext
    ext x
    rfl

def transport {A B : Type*} (e : A ≃ B) : Inv A ≃ Inv B :=
  e.permCongr.subtypeEquiv fun f => by
    constructor
    · intro h y
      simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using
        congrArg e (h (e.symm y))
    · intro h x
      apply e.injective
      simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using h (e x)

theorem option_reconstruction_iff {A : Type*} [DecidableEq A]
    (p : Option A) (f : Equiv.Perm A) :
    Function.Involutive (Equiv.Perm.decomposeOption.symm (p, f)) ↔
      Function.Involutive f ∧ ∀ a, p = some a → f a = a := by
  cases p with
  | none =>
    constructor
    · intro h
      refine ⟨fun a => ?_, by simp⟩
      simpa using h (some a)
    · rintro ⟨h, _⟩ (_ | a)
      · rfl
      · simpa using congrArg some (h a)
  | some a =>
    have eval_none : Equiv.Perm.decomposeOption.symm (some a, f) none = some a := by simp
    have eval_some (x : A) :
        Equiv.Perm.decomposeOption.symm (some a, f) (some x) =
          Equiv.swap none (some a) (some (f x)) := by simp
    constructor
    · intro h
      have hfix : f a = a := by
        have hn := h none
        rw [eval_none, eval_some, Equiv.swap_apply_eq_iff] at hn
        simpa using hn
      refine ⟨?_, ?_⟩
      · intro x
        by_cases hx : x = a
        · simp [hx, hfix]
        · have hfx : f x ≠ a := by
            intro he
            exact hx (f.injective (he.trans hfix.symm))
          have hffx : f (f x) ≠ a := by
            intro he
            exact hfx (f.injective (he.trans hfix.symm))
          have hh := h (some x)
          simpa [eval_some, Equiv.swap_apply_def, hfx, hffx] using hh
      · intro b hab
        cases Option.some.inj hab
        exact hfix
    · rintro ⟨h, hf⟩
      have hfix := hf a rfl
      rintro (_ | x)
      · simp [hfix]
      · by_cases hx : x = a
        · simp [hx, hfix]
        · have hfx : f x ≠ a := by
            intro he
            exact hx (f.injective (he.trans hfix.symm))
          simp [Equiv.swap_apply_def, hfx, h x, hx]

def optionDataEquiv {A : Type*} [DecidableEq A] :
    Inv (Option A) ≃
      {z : Option A × Equiv.Perm A //
        Function.Involutive z.2 ∧ ∀ a, z.1 = some a → z.2 a = a} :=
  Equiv.Perm.decomposeOption.subtypeEquiv fun f => by
    rw [← option_reconstruction_iff]
    change Function.Involutive f ↔
      Function.Involutive (Equiv.Perm.decomposeOption.symm (Equiv.Perm.decomposeOption f))
    rw [Equiv.symm_apply_apply]

def fixedPointEquiv {A : Type*} [DecidableEq A] (a : A) :
    {f : Equiv.Perm A // Function.Involutive f ∧ f a = a} ≃ Inv {x : A // x ≠ a} where
  toFun f := ⟨f.1.subtypePerm (fun x => by
    constructor
    · intro h hx
      exact h (hx ▸ f.2.2)
    · intro h hx
      exact h (f.1.injective (hx.trans f.2.2.symm))), by
        intro x
        apply Subtype.ext
        exact f.2.1 x.1⟩
  invFun f := ⟨Equiv.Perm.ofSubtype f.1, by
    constructor
    · intro x
      by_cases hx : x ≠ a
      · rw [Equiv.Perm.ofSubtype_apply_of_mem (p := fun x : A => x ≠ a) (a := x) f.1 hx,
          Equiv.Perm.ofSubtype_apply_coe]
        exact congrArg Subtype.val (f.2 ⟨x, hx⟩)
      · simp only [not_not] at hx
        subst x
        have ha := Equiv.Perm.ofSubtype_apply_of_not_mem (a := a) f.1 (by simp)
        rw [ha, ha]
    · exact Equiv.Perm.ofSubtype_apply_of_not_mem f.1 (by simp)⟩
  left_inv f := by
    apply Subtype.ext
    ext x
    by_cases hx : x ≠ a
    · simp [Equiv.Perm.ofSubtype_apply_of_mem, hx]
    · simp only [not_not] at hx
      subst x
      rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ (by simp)]
      exact f.2.2.symm
  right_inv f := by
    apply Subtype.ext
    ext x
    simp

def dataBranchesEquiv {A : Type*} :
    {z : Option A × Equiv.Perm A //
      Function.Involutive z.2 ∧ ∀ a, z.1 = some a → z.2 a = a} ≃
      Inv A ⊕ (Σ a : A, {f : Equiv.Perm A // Function.Involutive f ∧ f a = a}) where
  toFun z := match h : z.1.1 with
    | none => Sum.inl ⟨z.1.2, z.2.1⟩
    | some a => Sum.inr ⟨a, z.1.2, z.2.1, z.2.2 a h⟩
  invFun z := match z with
    | Sum.inl f => ⟨(none, f.1), f.2, by simp⟩
    | Sum.inr ⟨a, f⟩ => ⟨(some a, f.1), f.2.1, by
        intro b hab
        cases Option.some.inj hab
        exact f.2.2⟩
  left_inv z := by
    rcases z with ⟨⟨(_ | a), f⟩, h⟩ <;> rfl
  right_inv z := by
    rcases z with f | ⟨a, f⟩ <;> rfl

def recursionEquiv {A : Type*} [DecidableEq A] :
    Inv (Option A) ≃ Inv A ⊕ (Σ a : A, Inv {x : A // x ≠ a}) :=
  optionDataEquiv.trans (dataBranchesEquiv.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.sigmaCongrRight fixedPointEquiv)))

def count (n : ℕ) : ℕ := Nat.card (Inv (Fin n))

theorem card_eq_count (A : Type*) [Fintype A] :
    Nat.card (Inv A) = count (Fintype.card A) :=
  Nat.card_congr (transport (Fintype.equivFin A))

theorem card_ne (A : Type*) [Fintype A] [DecidableEq A] (a : A) :
    Fintype.card {x : A // x ≠ a} = Fintype.card A - 1 := by
  classical
  simp [Fintype.card_subtype_compl]

theorem count_step (n : ℕ) : count (n + 2) = count (n + 1) + (n + 1) * count n := by
  classical
  calc
    count (n + 2) = Nat.card (Inv (Option (Fin (n + 1)))) :=
      Nat.card_congr (transport (finSuccEquiv (n + 1)))
    _ = Nat.card (Inv (Fin (n + 1)) ⊕ (Σ a : Fin (n + 1), Inv {x : Fin (n + 1) // x ≠ a})) :=
      Nat.card_congr recursionEquiv
    _ = count (n + 1) + (n + 1) * count n := by
      rw [Nat.card_sum, Nat.card_sigma]
      simp only [card_eq_count, card_ne, Fintype.card_fin, Nat.add_sub_cancel]
      simp [count]

theorem count_zero : count 0 = 1 := by
  letI : Nonempty (Inv (Fin 0)) := ⟨⟨Equiv.refl _, fun _ => rfl⟩⟩
  exact Nat.card_unique

theorem count_one : count 1 = 1 := by
  letI : Nonempty (Inv (Fin 1)) := ⟨⟨Equiv.refl _, fun _ => rfl⟩⟩
  exact Nat.card_unique

theorem count_five : count 5 = 26 := by
  norm_num [count_step, count_zero, count_one]

theorem source_count (S : Finset ℕ) (hS : S = {1, 2, 3, 4, 5}) :
    Nat.card {f : S → S // Function.Involutive f} = 26 := by
  classical
  rw [Nat.card_congr (functionEquiv S), card_eq_count]
  have hc : Fintype.card S = 5 := by simp [hS]
  rw [hc, count_five]

end FiniteInvolutionEnumeration

theorem solution (S : Finset ℕ) (hS : S = {1, 2, 3, 4, 5}) :
    ∃ f : ℕ → ℕ, ∀ x ∈ S, f (f x) = x := by
  subst S
  exact ⟨id, fun _ _ => rfl⟩

#print axioms FiniteInvolutionEnumeration.functionEquiv
#print axioms FiniteInvolutionEnumeration.transport
#print axioms FiniteInvolutionEnumeration.option_reconstruction_iff
#print axioms FiniteInvolutionEnumeration.optionDataEquiv
#print axioms FiniteInvolutionEnumeration.fixedPointEquiv
#print axioms FiniteInvolutionEnumeration.dataBranchesEquiv
#print axioms FiniteInvolutionEnumeration.recursionEquiv
#print axioms FiniteInvolutionEnumeration.count
#print axioms FiniteInvolutionEnumeration.card_eq_count
#print axioms FiniteInvolutionEnumeration.card_ne
#print axioms FiniteInvolutionEnumeration.count_step
#print axioms FiniteInvolutionEnumeration.count_zero
#print axioms FiniteInvolutionEnumeration.count_one
#print axioms FiniteInvolutionEnumeration.count_five
#print axioms FiniteInvolutionEnumeration.source_count
#print axioms solution
