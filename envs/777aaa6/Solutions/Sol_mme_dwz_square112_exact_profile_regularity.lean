-- Prove2me | solution 1 for mme_dwz_square112_exact_profile_regularity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T08:06:30.456725+00:00
-- url     : https://prove2.me/submissions/fb88ee76-a5dc-4a7b-ac28-51ecbc83c672

import Definitions.Def_mme_dwz_square112_exact_profile_data
import Theorems.Thm_mme_dwz_square112_exact_profile_marginals_and_fibers
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Logic.Equiv.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

open MME.DWZSquare112
open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution (N : ℕ) (c : Fin 4 → ℕ) (hcount : ∑ r, c r = N) :
    let M : Fin 3 → Type := fun i =>
      {x : Fin N → Fin 3 // ∀ a : Fin 3,
        Fintype.card {j : Fin N // x j = a} = marginal c i a}
    let F : Fin 3 → ℕ := fun i => ∏ a : Fin 3,
      (marginal c i a).factorial /
        ∏ r : {r : Fin 4 // row r i = a}, (c r.1).factorial
    let J := Nat.card (ExactWord N c)
    0 < J ∧
      (∀ i : Fin 3, J = Nat.card (M i) * F i) ∧
      0 < (∏ i : Fin 3, Nat.card (M i)) ∧
      0 < (∏ i : Fin 3, F i) ∧
      J ^ 3 = (∏ i : Fin 3, Nat.card (M i)) * (∏ i : Fin 3, F i) := by
  classical
  dsimp only
  let M : Fin 3 → Type := fun i =>
    {x : Fin N → Fin 3 // ∀ a : Fin 3,
      Fintype.card {j : Fin N // x j = a} = marginal c i a}
  let F : Fin 3 → ℕ := fun i => ∏ a : Fin 3,
    (marginal c i a).factorial /
      ∏ r : {r : Fin 4 // row r i = a}, (c r.1).factorial
  letI : Fintype (ExactWord N c) := by
    unfold ExactWord
    infer_instance
  letI (i : Fin 3) : Fintype (M i) := by
    dsimp [M]
    infer_instance
  have hJ : 0 < Nat.card (ExactWord N c) := by
    have hcard := mme_fintype_prescribed_fiber_function_card
      (α := Fin N) c (by simpa using hcount)
    simp only [Fintype.card_fin] at hcard
    have hmult : Fintype.card (ExactWord N c) =
        Nat.multinomial Finset.univ c := by
      simp only [Nat.multinomial, hcount]
      convert hcard using 1
      exact congrArg (fun inst : Fintype (ExactWord N c) => @Fintype.card _ inst)
        (Subsingleton.elim _ _)
    rw [Nat.card_eq_fintype_card, hmult]
    exact Nat.multinomial_pos Finset.univ c
  have hfactor (i : Fin 3) : Nat.card (ExactWord N c) = Nat.card (M i) * F i := by
    let f : ExactWord N c → M i := fun w =>
      ⟨modeWord w i,
        fun a => (mme_dwz_square112_exact_profile_marginals_and_fibers N c).1 w i a⟩
    have hfiber (x : M i) : Nat.card {w : ExactWord N c // f w = x} = F i := by
      let e : {w : ExactWord N c // f w = x} ≃
          {w : ExactWord N c // modeWord w i = x.1} :=
        { toFun := fun w => ⟨w.1, congrArg Subtype.val w.2⟩
          invFun := fun w => ⟨w.1, Subtype.ext w.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact (Nat.card_congr e).trans
        ((mme_dwz_square112_exact_profile_marginals_and_fibers N c).2 i x.1 x.2)
    calc
      Nat.card (ExactWord N c) =
          Nat.card (Σ x : M i, {w : ExactWord N c // f w = x}) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
      _ = ∑ x : M i, Nat.card {w : ExactWord N c // f w = x} := Nat.card_sigma
      _ = ∑ _x : M i, F i := Finset.sum_congr rfl (fun x _ => hfiber x)
      _ = Nat.card (M i) * F i := by simp [Nat.card_eq_fintype_card]
  have hpositive (i : Fin 3) : 0 < Nat.card (M i) ∧ 0 < F i := by
    have hp : 0 < Nat.card (M i) * F i := (hfactor i) ▸ hJ
    exact ⟨Nat.pos_of_mul_pos_right hp, Nat.pos_of_mul_pos_left hp⟩
  refine ⟨hJ, hfactor,
    Finset.prod_pos (fun i _ => (hpositive i).1),
    Finset.prod_pos (fun i _ => (hpositive i).2), ?_⟩
  calc
    Nat.card (ExactWord N c) ^ 3 = ∏ _i : Fin 3, Nat.card (ExactWord N c) := by simp
    _ = ∏ i : Fin 3, Nat.card (M i) * F i :=
      Finset.prod_congr rfl (fun i _ => hfactor i)
    _ = (∏ i : Fin 3, Nat.card (M i)) * (∏ i : Fin 3, F i) :=
      Finset.prod_mul_distrib
