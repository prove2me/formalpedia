-- Prove2me | solution 1 for mme_fintype_prescribed_fiber_function_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:04:00.262712+00:00
-- url     : https://prove2.me/submissions/3d8f249a-f19b-4afa-afff-6e0568498e4a

import Theorems.Thm_mme_fintype_fixed_fiber_function_card

open Equiv

set_option autoImplicit false

/-- A finite histogram whose total is the domain size is realizable, and the
corresponding functions are counted by the multinomial coefficient. -/
theorem solution
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (k : ι → ℕ) (hsum : ∑ i, k i = Fintype.card α) :
    Fintype.card
        {g : α → ι // ∀ i,
          Fintype.card {a // g a = i} = k i} =
      (Fintype.card α).factorial / ∏ i, (k i).factorial := by
  classical
  let β := Σ i : ι, Fin (k i)
  let e : α ≃ β := Fintype.equivOfCardEq (by
    rw [Fintype.card_sigma]
    simpa using hsum.symm)
  let f : α → ι := fun a => (e a).1
  have hfiber : ∀ i,
      Fintype.card {a // f a = i} = k i := by
    intro i
    let e₁ : {a // f a = i} ≃ {b : β // b.1 = i} :=
      Equiv.subtypeEquiv e (fun a => by rfl)
    calc
      Fintype.card {a // f a = i} =
          Fintype.card {b : β // b.1 = i} := Fintype.card_congr e₁
      _ = Fintype.card (Fin (k i)) :=
        Fintype.card_congr (Equiv.sigmaSubtype i)
      _ = k i := Fintype.card_fin _
  let profileEquiv :
      {g : α → ι // ∀ i, Fintype.card {a // g a = i} = k i} ≃
      {g : α → ι // ∀ i,
        Fintype.card {a // g a = i} =
          Fintype.card {a // f a = i}} :=
    Equiv.subtypeEquiv (Equiv.refl (α → ι)) (fun g => by
      constructor
      · intro hg i
        simpa only [hfiber] using hg i
      · intro hg i
        simpa only [hfiber] using hg i)
  rw [Fintype.card_congr profileEquiv,
    mme_fintype_fixed_fiber_function_card f]
  apply congrArg ((Fintype.card α).factorial / ·)
  apply Finset.prod_congr rfl
  intro i hi
  rw [hfiber]
