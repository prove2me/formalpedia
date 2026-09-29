-- Prove2me | solution 1 for mme_stothers_phi224_exact_profile_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:32:01.65805+00:00
-- url     : https://prove2.me/submissions/67285513-3b6a-426b-8661-4250aa3caa89

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + 2 * beta + gamma + delta = N) :
    Nat.card
        (MME.StothersFourth.Phi224.ExactProfileWord
          N alpha beta gamma delta) =
      (2 * N).factorial /
        ∏ r : Fin 9,
          (MME.StothersFourth.Phi224.profileMultiplicity
            alpha beta gamma delta r).factorial := by
  classical
  let multiplicity : Fin 9 → ℕ :=
    MME.StothersFourth.Phi224.profileMultiplicity
      alpha beta gamma delta
  have htotal : (∑ r : Fin 9, multiplicity r) = 2 * N := by
    simp [multiplicity,
      MME.StothersFourth.Phi224.profileMultiplicity,
      Fin.sum_univ_succ]
    omega
  have htotalCard :
      (∑ r : Fin 9, multiplicity r) =
        Fintype.card (Fin (2 * N)) := by
    simpa using htotal
  let Assignment :=
    {w : Fin (2 * N) → Fin 9 //
      ∀ r, Fintype.card {j // w j = r} = multiplicity r}
  let ftGeneric : Fintype Assignment :=
    @Subtype.fintype _ _
      (fun _ => Fintype.decidableForallFintype) Pi.instFintype
  have hgeneric :
      @Fintype.card Assignment ftGeneric =
        (2 * N).factorial / ∏ r : Fin 9, (multiplicity r).factorial := by
    simpa only [Assignment, Fintype.card_fin] using
      (mme_fintype_prescribed_fiber_function_card
        (α := Fin (2 * N)) (ι := Fin 9) multiplicity htotalCard)
  let e :
      MME.StothersFourth.Phi224.ExactProfileWord
          N alpha beta gamma delta ≃ Assignment := {
    toFun w := ⟨w.1, by
      intro r
      rw [Fintype.card_subtype]
      exact w.2 r⟩
    invFun w := ⟨w.1, by
      intro r
      rw [← Fintype.card_subtype]
      exact w.2 r⟩
    left_inv w := by
      apply Subtype.ext
      rfl
    right_inv w := by
      apply Subtype.ext
      rfl
  }
  calc
    Nat.card
        (MME.StothersFourth.Phi224.ExactProfileWord
          N alpha beta gamma delta) = Nat.card Assignment :=
      Nat.card_congr e
    _ = @Fintype.card Assignment inferInstance :=
      Nat.card_eq_fintype_card
    _ = @Fintype.card Assignment ftGeneric :=
      @Fintype.card_congr Assignment Assignment inferInstance ftGeneric
        (Equiv.refl Assignment)
    _ = (2 * N).factorial /
        ∏ r : Fin 9, (multiplicity r).factorial := hgeneric
    _ = (2 * N).factorial /
        ∏ r : Fin 9,
          (MME.StothersFourth.Phi224.profileMultiplicity
            alpha beta gamma delta r).factorial := rfl
