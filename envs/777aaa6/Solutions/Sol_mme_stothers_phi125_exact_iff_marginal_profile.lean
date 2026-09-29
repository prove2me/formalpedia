-- Prove2me | solution 1 for mme_stothers_phi125_exact_iff_marginal_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:52:12.96846+00:00
-- url     : https://prove2.me/submissions/eddb9333-87b3-4dfd-bc6d-e4118071a421

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi125_profile_data

open BigOperators

namespace MME.StothersFourth.Phi125

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

private theorem projectedFiberCard
    {N : ℕ} (w : ProfileWord N) (i : Fin 3) (s : Fin 5) :
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => modeWord w i j = s)).card =
      ∑ r : {r : Fin 6 // pattern r i = s},
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => w j = r.1)).card := by
  classical
  let e :
      {j : Fin (2 * N) // modeWord w i j = s} ≃
        Sigma fun r : {r : Fin 6 // pattern r i = s} =>
          {j : Fin (2 * N) // w j = r.1} := {
    toFun j := ⟨⟨w j.1, j.2⟩, ⟨j.1, rfl⟩⟩
    invFun x := ⟨x.2.1, by
      change pattern (w x.2.1) i = s
      rw [x.2.2]
      exact x.1.2⟩
    left_inv j := by
      apply Subtype.ext
      rfl
    right_inv x := by
      rcases x with ⟨⟨r, hr⟩, ⟨j, hj⟩⟩
      cases hj
      rfl
  }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Fintype.card_subtype]

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

theorem pattern_injective : Function.Injective pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [pattern] at h0 h1 h2 ⊢

theorem exact_profile_implies_marginal_profile
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N)
    (w : ProfileWord N)
    (hexact : ∀ r : Fin 6,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card =
          profileMultiplicity alpha beta gamma r) :
    ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => modeWord w i j = s)).card =
          marginalMultiplicity N alpha beta gamma i s := by
  intro i s
  rw [projectedFiberCard]
  rw [← sum_ite_eq_sum_subtype
    (fun r : Fin 6 => pattern r i) s
    (fun r =>
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card)]
  simp_rw [hexact]
  fin_cases i <;> fin_cases s <;>
    simp [pattern, profileMultiplicity, marginalMultiplicity,
      Fin.sum_univ_succ] <;> omega

theorem marginal_profile_implies_exact_profile
    (N alpha beta gamma : ℕ)
    (w : ProfileWord N)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => modeWord w i j = s)).card =
          marginalMultiplicity N alpha beta gamma i s) :
    ∀ r : Fin 6,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j => w j = r)).card =
          profileMultiplicity alpha beta gamma r := by
  let k : Fin 6 → ℕ := fun r =>
    ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j => w j = r)).card
  have h04 := hmarginal 2 4
  have h01 := hmarginal 2 1
  have h10 := hmarginal 1 0
  have h12 := hmarginal 1 2
  have h22 := hmarginal 2 2
  have h23 := hmarginal 2 3
  rw [projectedFiberCard] at h04 h01 h10 h12 h22 h23
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 6 => pattern r 2) (4 : Fin 5) k] at h04
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 6 => pattern r 2) (1 : Fin 5) k] at h01
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 6 => pattern r 1) (0 : Fin 5) k] at h10
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 6 => pattern r 1) (2 : Fin 5) k] at h12
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 6 => pattern r 2) (2 : Fin 5) k] at h22
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 6 => pattern r 2) (3 : Fin 5) k] at h23
  change (∑ r : Fin 6, if pattern r 2 = 4 then k r else 0) =
    alpha at h04
  change (∑ r : Fin 6, if pattern r 2 = 1 then k r else 0) =
    alpha at h01
  change (∑ r : Fin 6, if pattern r 1 = 0 then k r else 0) =
    alpha + gamma at h10
  change (∑ r : Fin 6, if pattern r 1 = 2 then k r else 0) =
    alpha + gamma at h12
  change (∑ r : Fin 6, if pattern r 2 = 2 then k r else 0) =
    beta + gamma at h22
  change (∑ r : Fin 6, if pattern r 2 = 3 then k r else 0) =
    beta + gamma at h23
  simp [pattern, Fin.sum_univ_succ] at h04 h01 h10 h12 h22 h23
  intro r
  change k r = profileMultiplicity alpha beta gamma r
  fin_cases r <;> simp [profileMultiplicity] <;> omega

end MME.StothersFourth.Phi125

theorem solution
    (N alpha beta gamma : ℕ) (hsum : alpha + beta + gamma = N) :
    Function.Injective MME.StothersFourth.Phi125.pattern ∧
    ∀ w : MME.StothersFourth.Phi125.ProfileWord N,
      ((∀ r : Fin 6,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j => w j = r)).card =
            MME.StothersFourth.Phi125.profileMultiplicity
              alpha beta gamma r) ↔
       (∀ i : Fin 3, ∀ s : Fin 5,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j =>
            MME.StothersFourth.Phi125.modeWord w i j = s)).card =
            MME.StothersFourth.Phi125.marginalMultiplicity
              N alpha beta gamma i s)) := by
  refine ⟨MME.StothersFourth.Phi125.pattern_injective, ?_⟩
  intro w
  constructor
  · exact MME.StothersFourth.Phi125.exact_profile_implies_marginal_profile
      N alpha beta gamma hsum w
  · exact MME.StothersFourth.Phi125.marginal_profile_implies_exact_profile
      N alpha beta gamma w
