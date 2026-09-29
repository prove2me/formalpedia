-- Prove2me | solution 1 for mme_stothers_phi224_fixed_mode_exact_profile_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:24:23.531285+00:00
-- url     : https://prove2.me/submissions/dda2ce10-e0bb-4571-aeed-607746d09a53

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_exact_profile_marginals
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
    ((Finset.univ : Finset beta).filter (fun b ↦ q b = i))
    (fun b ↦ by simp) f

/-- The exact phi_224 family has a uniform, explicitly multinomial fibre
over every realized word in each tensor mode. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + 2 * beta + gamma + delta = N)
    (w : MME.StothersFourth.Phi224.ExactProfileWord
      N alpha beta gamma delta)
    (i : Fin 3) :
    Nat.card
        {v : MME.StothersFourth.Phi224.ExactProfileWord
            N alpha beta gamma delta //
          MME.StothersFourth.Phi224.modeWord v.1 i =
            MME.StothersFourth.Phi224.modeWord w.1 i} =
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r i = s},
            (MME.StothersFourth.Phi224.profileMultiplicity
              alpha beta gamma delta r.1).factorial := by
  classical
  let multiplicity : Fin 9 → ℕ :=
    MME.StothersFourth.Phi224.profileMultiplicity
      alpha beta gamma delta
  let Assignment :=
    {g : Fin (2 * N) → Fin 9 //
      (∀ j,
        MME.StothersFourth.Phi224.pattern (g j) i =
          MME.StothersFourth.Phi224.modeWord w.1 i j) ∧
      ∀ r, Fintype.card {j // g j = r} = multiplicity r}
  let Fiber :=
    {v : MME.StothersFourth.Phi224.ExactProfileWord
        N alpha beta gamma delta //
      MME.StothersFourth.Phi224.modeWord v.1 i =
        MME.StothersFourth.Phi224.modeWord w.1 i}
  let e : Fiber ≃ Assignment := {
    toFun v := ⟨v.1.1, by
      constructor
      · intro j
        exact congrFun v.2 j
      · intro r
        rw [Fintype.card_subtype]
        exact v.1.2 r⟩
    invFun G := by
      let v : MME.StothersFourth.Phi224.ExactProfileWord
          N alpha beta gamma delta := ⟨G.1, by
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
          (fun j ↦
            MME.StothersFourth.Phi224.modeWord w.1 l j = s)).card =
          MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta l s := by
    exact (mme_stothers_phi224_exact_profile_marginals
      N alpha beta gamma delta hsum).2.2 w.1 w.2
  have hprofileSum (s : Fin 5) :
      (∑ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r i = s},
        multiplicity r.1) =
          MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s := by
    rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦
        MME.StothersFourth.Phi224.pattern r i) s multiplicity]
    fin_cases i <;> fin_cases s <;>
      simp [multiplicity,
        MME.StothersFourth.Phi224.pattern,
        MME.StothersFourth.Phi224.profileMultiplicity,
        MME.StothersFourth.Phi224.marginalMultiplicity,
        Fin.sum_univ_succ] <;> omega
  have hconstraint (s : Fin 5) :
      (∑ r : {r : Fin 9 //
          MME.StothersFourth.Phi224.pattern r i = s},
        multiplicity r.1) =
        Fintype.card {j : Fin (2 * N) //
          MME.StothersFourth.Phi224.modeWord w.1 i j = s} := by
    rw [hprofileSum s, Fintype.card_subtype, hmarginal i s]
  have hassignment :
      Nat.card Assignment =
        ∏ s : Fin 5,
          (Fintype.card {j : Fin (2 * N) //
            MME.StothersFourth.Phi224.modeWord w.1 i j = s}).factorial /
            ∏ r : {r : Fin 9 //
                MME.StothersFourth.Phi224.pattern r i = s},
              (multiplicity r.1).factorial := by
    simpa only [Assignment] using
      (mme_fintype_constrained_prescribed_fiber_function_card
        (h := MME.StothersFourth.Phi224.modeWord w.1 i)
        (q := fun r : Fin 9 ↦
          MME.StothersFourth.Phi224.pattern r i)
        multiplicity hconstraint)
  calc
    Nat.card
        {v : MME.StothersFourth.Phi224.ExactProfileWord
            N alpha beta gamma delta //
          MME.StothersFourth.Phi224.modeWord v.1 i =
            MME.StothersFourth.Phi224.modeWord w.1 i} =
        Nat.card Fiber := rfl
    _ = Nat.card Assignment := Nat.card_congr e
    _ = ∏ s : Fin 5,
        (Fintype.card {j : Fin (2 * N) //
          MME.StothersFourth.Phi224.modeWord w.1 i j = s}).factorial /
          ∏ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r i = s},
            (multiplicity r.1).factorial := hassignment
    _ = ∏ s : Fin 5,
        (MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r i = s},
            (multiplicity r.1).factorial := by
      apply Finset.prod_congr rfl
      intro s hs
      rw [Fintype.card_subtype, hmarginal i s]
    _ = ∏ s : Fin 5,
        (MME.StothersFourth.Phi224.marginalMultiplicity
          alpha beta gamma delta i s).factorial /
          ∏ r : {r : Fin 9 //
              MME.StothersFourth.Phi224.pattern r i = s},
            (MME.StothersFourth.Phi224.profileMultiplicity
              alpha beta gamma delta r.1).factorial := rfl
