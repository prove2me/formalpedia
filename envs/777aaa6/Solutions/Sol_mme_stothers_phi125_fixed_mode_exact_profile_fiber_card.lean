-- Prove2me | solution 1 for mme_stothers_phi125_fixed_mode_exact_profile_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:58:18.358615+00:00
-- url     : https://prove2.me/submissions/add4ddee-2fd6-4d50-ae8b-0dce02a853b9

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi125_profile_data
import Theorems.Thm_mme_stothers_phi125_exact_iff_marginal_profile
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

private theorem sum_ite_eq_sum_subtype
    {beta iota M : Type*} [Fintype beta] [DecidableEq iota]
    [AddCommMonoid M] (q : beta → iota) (i : iota) (f : beta → M) :
    (∑ b : beta, if q b = i then f b else 0) =
      ∑ b : {b : beta // q b = i}, f b.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    ((Finset.univ : Finset beta).filter (fun b => q b = i))
    (fun b => by simp) f

theorem solution
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N)
    (w : MME.StothersFourth.Phi125.ExactProfileWord
      N alpha beta gamma)
    (i : Fin 3) :
    Nat.card
        {v : MME.StothersFourth.Phi125.ExactProfileWord
            N alpha beta gamma //
          MME.StothersFourth.Phi125.modeWord v.1 i =
            MME.StothersFourth.Phi125.modeWord w.1 i} =
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi125.marginalMultiplicity
          N alpha beta gamma i s).factorial /
          ∏ r : {r : Fin 6 //
              MME.StothersFourth.Phi125.pattern r i = s},
            (MME.StothersFourth.Phi125.profileMultiplicity
              alpha beta gamma r.1).factorial := by
  classical
  let multiplicity : Fin 6 → ℕ :=
    MME.StothersFourth.Phi125.profileMultiplicity alpha beta gamma
  let Assignment :=
    {g : Fin (2 * N) → Fin 6 //
      (∀ j,
        MME.StothersFourth.Phi125.pattern (g j) i =
          MME.StothersFourth.Phi125.modeWord w.1 i j) ∧
      ∀ r, Fintype.card {j // g j = r} = multiplicity r}
  let Fiber :=
    {v : MME.StothersFourth.Phi125.ExactProfileWord
        N alpha beta gamma //
      MME.StothersFourth.Phi125.modeWord v.1 i =
        MME.StothersFourth.Phi125.modeWord w.1 i}
  let e : Fiber ≃ Assignment := {
    toFun v := ⟨v.1.1, by
      constructor
      · intro j
        exact congrFun v.2 j
      · intro r
        rw [Fintype.card_subtype]
        exact v.1.2 r⟩
    invFun G := by
      let v : MME.StothersFourth.Phi125.ExactProfileWord
          N alpha beta gamma := ⟨G.1, by
        intro r
        rw [← Fintype.card_subtype]
        exact G.2.2 r⟩
      refine ⟨v, ?_⟩
      funext j
      exact G.2.1 j
    left_inv v := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv G := by
      apply Subtype.ext
      rfl
  }
  have hmarginal :
      ∀ l : Fin 3, ∀ s : Fin 5,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j =>
            MME.StothersFourth.Phi125.modeWord w.1 l j = s)).card =
          MME.StothersFourth.Phi125.marginalMultiplicity
            N alpha beta gamma l s :=
    ((mme_stothers_phi125_exact_iff_marginal_profile
      N alpha beta gamma hsum).2 w.1).mp w.2
  have hprofileSum (s : Fin 5) :
      (∑ r : {r : Fin 6 //
          MME.StothersFourth.Phi125.pattern r i = s},
        multiplicity r.1) =
          MME.StothersFourth.Phi125.marginalMultiplicity
            N alpha beta gamma i s := by
    rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 6 =>
        MME.StothersFourth.Phi125.pattern r i) s multiplicity]
    fin_cases i <;> fin_cases s <;>
      simp [multiplicity,
        MME.StothersFourth.Phi125.pattern,
        MME.StothersFourth.Phi125.profileMultiplicity,
        MME.StothersFourth.Phi125.marginalMultiplicity,
        Fin.sum_univ_succ] <;> omega
  have hconstraint (s : Fin 5) :
      (∑ r : {r : Fin 6 //
          MME.StothersFourth.Phi125.pattern r i = s},
        multiplicity r.1) =
        Fintype.card {j : Fin (2 * N) //
          MME.StothersFourth.Phi125.modeWord w.1 i j = s} := by
    rw [hprofileSum s, Fintype.card_subtype, hmarginal i s]
  have hassignment :
      Nat.card Assignment =
        ∏ s : Fin 5,
          (Fintype.card {j : Fin (2 * N) //
            MME.StothersFourth.Phi125.modeWord w.1 i j = s}).factorial /
            ∏ r : {r : Fin 6 //
                MME.StothersFourth.Phi125.pattern r i = s},
              (multiplicity r.1).factorial := by
    simpa only [Assignment] using
      (mme_fintype_constrained_prescribed_fiber_function_card
        (h := MME.StothersFourth.Phi125.modeWord w.1 i)
        (q := fun r : Fin 6 =>
          MME.StothersFourth.Phi125.pattern r i)
        multiplicity hconstraint)
  calc
    Nat.card
        {v : MME.StothersFourth.Phi125.ExactProfileWord
            N alpha beta gamma //
          MME.StothersFourth.Phi125.modeWord v.1 i =
            MME.StothersFourth.Phi125.modeWord w.1 i} =
        Nat.card Fiber := rfl
    _ = Nat.card Assignment := Nat.card_congr e
    _ = ∏ s : Fin 5,
        (Fintype.card {j : Fin (2 * N) //
          MME.StothersFourth.Phi125.modeWord w.1 i j = s}).factorial /
          ∏ r : {r : Fin 6 //
              MME.StothersFourth.Phi125.pattern r i = s},
            (multiplicity r.1).factorial := hassignment
    _ = ∏ s : Fin 5,
        (MME.StothersFourth.Phi125.marginalMultiplicity
          N alpha beta gamma i s).factorial /
          ∏ r : {r : Fin 6 //
              MME.StothersFourth.Phi125.pattern r i = s},
            (multiplicity r.1).factorial := by
      apply Finset.prod_congr rfl
      intro s hs
      rw [Fintype.card_subtype, hmarginal i s]
    _ = ∏ s : Fin 5,
        (MME.StothersFourth.Phi125.marginalMultiplicity
          N alpha beta gamma i s).factorial /
          ∏ r : {r : Fin 6 //
              MME.StothersFourth.Phi125.pattern r i = s},
            (MME.StothersFourth.Phi125.profileMultiplicity
              alpha beta gamma r.1).factorial := rfl
