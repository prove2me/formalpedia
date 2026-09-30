-- Prove2me | solution 1 for lean_workbook_plus_52965
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:54:08.881635+00:00
-- url     : https://prove2.me/submissions/996e4611-9a82-4a48-9ea6-b6018874991a

import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

def fiberInvolutionEquiv (A B : Type*) :
    {f : A × B → A × B // Function.Involutive f ∧ ∀ x, (f x).1 = x.1} ≃
      (A → {g : B → B // Function.Involutive g}) where
  toFun f a := ⟨fun b => (f.1 (a, b)).2, by
    intro b
    have he : (a, (f.1 (a, b)).2) = f.1 (a, b) :=
      Prod.ext (f.2.2 (a, b)).symm rfl
    change (f.1 (a, (f.1 (a, b)).2)).2 = b
    rw [he]
    exact congrArg Prod.snd (f.2.1 (a, b))⟩
  invFun g := ⟨fun x => (x.1, (g x.1).1 x.2), by
    constructor
    · rintro ⟨a, b⟩
      exact Prod.ext rfl ((g a).2 b)
    · intro x
      rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    exact Prod.ext (f.2.2 x).symm rfl
  right_inv g := by
    funext a
    apply Subtype.ext
    rfl

def coordinateInvolutionEquiv {X A B : Type*} (e : X ≃ A × B) :
    {f : X → X // Function.Involutive f ∧ ∀ x, (e (f x)).1 = (e x).1} ≃
      {f : A × B → A × B // Function.Involutive f ∧ ∀ x, (f x).1 = x.1} where
  toFun f := ⟨fun x => e (f.1 (e.symm x)), by
    constructor
    · intro x
      simp only [Equiv.symm_apply_apply]
      rw [f.2.1 (e.symm x)]
      exact e.apply_symm_apply x
    · intro x
      simpa only [Equiv.apply_symm_apply] using f.2.2 (e.symm x)⟩
  invFun f := ⟨fun x => e.symm (f.1 (e x)), by
    constructor
    · intro x
      simp only [Equiv.apply_symm_apply]
      rw [f.2.1 (e x)]
      exact e.symm_apply_apply x
    · intro x
      simpa only [Equiv.apply_symm_apply] using f.2.2 (e x)⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    simp only [Equiv.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    funext x
    simp only [Equiv.apply_symm_apply]

abbrev PositiveTwelve := {n : ℕ // n ∈ Finset.Icc 1 12}

def positiveTwelveEquiv : PositiveTwelve ≃ Fin 12 where
  toFun x := ⟨x.1 - 1, by have hx := Finset.mem_Icc.mp x.2; omega⟩
  invFun x := ⟨x.1 + 1, by simp only [Finset.mem_Icc]; omega⟩
  left_inv x := by
    apply Subtype.ext
    have hx := Finset.mem_Icc.mp x.2
    change x.1 - 1 + 1 = x.1
    omega
  right_inv x := by
    apply Fin.ext
    change x.1 + 1 - 1 = x.1
    omega

def twelveResidueCoordinates : PositiveTwelve ≃ Fin 3 × Fin 4 :=
  positiveTwelveEquiv.trans
    ((finProdFinEquiv (m := 4) (n := 3)).symm.trans (Equiv.prodComm _ _))

theorem twelve_residue_coordinate_eq (x y : PositiveTwelve) :
    (twelveResidueCoordinates x).1 = (twelveResidueCoordinates y).1 ↔
      x.1 % 3 = y.1 % 3 := by
  rw [Fin.ext_iff]
  change (x.1 - 1) % 3 = (y.1 - 1) % 3 ↔ x.1 % 3 = y.1 % 3
  have hx := Finset.mem_Icc.mp x.2
  have hy := Finset.mem_Icc.mp y.2
  omega

local instance : DecidablePred (fun g : Fin 4 → Fin 4 => Function.Involutive g) :=
  fun g => inferInstanceAs (Decidable (∀ x, g (g x) = x))

theorem four_point_involution_count :
    Fintype.card {g : Fin 4 → Fin 4 // Function.Involutive g} = 10 := by
  decide

theorem residue_preserving_involution_count :
    Nat.card {f : PositiveTwelve → PositiveTwelve //
      Function.Involutive f ∧ ∀ x, (f x).1 % 3 = x.1 % 3} = 1000 := by
  let e1 := Equiv.subtypeEquivRight (fun f : PositiveTwelve → PositiveTwelve =>
    and_congr_right (fun (_hf : Function.Involutive f) =>
      forall_congr' (fun x => (twelve_residue_coordinate_eq (f x) x).symm)))
  let e := e1.trans ((coordinateInvolutionEquiv twelveResidueCoordinates).trans
    (fiberInvolutionEquiv (Fin 3) (Fin 4)))
  have h4 : Nat.card {g : Fin 4 → Fin 4 // Function.Involutive g} = 10 := by
    rw [Nat.card_eq_fintype_card]
    exact four_point_involution_count
  rw [Nat.card_congr e, Nat.card_fun, h4]
  norm_num

theorem involution_subtraction_residue_iff (f : PositiveTwelve → PositiveTwelve)
    (hf : Function.Involutive f) :
    (∀ x, ((f x).1 - x.1) % 3 = 0) ↔ ∀ x, (f x).1 % 3 = x.1 % 3 := by
  constructor
  · intro h x
    have h1 := h x
    have h2 := h (f x)
    rw [hf x] at h2
    omega
  · intro h x
    have hx := h x
    omega

theorem positive_twelve_involution_count :
    Nat.card {f : PositiveTwelve → PositiveTwelve //
      Function.Involutive f ∧ ∀ x, ((f x).1 - x.1) % 3 = 0} = 1000 := by
  let e := Equiv.subtypeEquivRight (fun f : PositiveTwelve → PositiveTwelve =>
    and_congr_right (involution_subtraction_residue_iff f))
  exact (Nat.card_congr e).trans residue_preserving_involution_count

theorem solution (S : Finset ℕ) (_hS : S = Finset.Icc 1 12) :
    ∃ f : ℕ → ℕ, ∀ x ∈ S, f (f x) = x ∧ (f x - x) % 3 = 0 := by
  exact ⟨id, fun _ _ => ⟨rfl, by simp⟩⟩
