-- Prove2me | solution 1 for mme_stothers_phi224_exact_profile_marginals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:26:31.067739+00:00
-- url     : https://prove2.me/submissions/de0a6ff4-e53c-431c-bc61-3b9265f588cf

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data

open BigOperators

namespace MME.StothersFourth.Phi224

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

private theorem projectedFiberCard
    {N : ℕ} (w : ProfileWord N) (i : Fin 3) (s : Fin 5) :
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ modeWord w i j = s)).card =
      ∑ r : {r : Fin 9 // pattern r i = s},
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ w j = r.1)).card := by
  classical
  let e :
      {j : Fin (2 * N) // modeWord w i j = s} ≃
        Sigma fun r : {r : Fin 9 // pattern r i = s} =>
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
    ((Finset.univ : Finset beta).filter (fun b ↦ q b = i))
    (fun b ↦ by simp) f

theorem pattern_injective : Function.Injective pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [pattern] at h0 h1 h2 ⊢

theorem profileMultiplicity_sum
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + 2 * beta + gamma + delta = N) :
    ∑ r : Fin 9, profileMultiplicity alpha beta gamma delta r = 2 * N := by
  simp [profileMultiplicity, Fin.sum_univ_succ]
  omega

theorem exact_profile_implies_marginal_profile
    (N alpha beta gamma delta : ℕ)
    (w : ProfileWord N)
    (hexact : ∀ r : Fin 9,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w j = r)).card =
          profileMultiplicity alpha beta gamma delta r) :
    ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ modeWord w i j = s)).card =
          marginalMultiplicity alpha beta gamma delta i s := by
  intro i s
  rw [projectedFiberCard]
  rw [← sum_ite_eq_sum_subtype
    (fun r : Fin 9 ↦ pattern r i) s
    (fun r ↦
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w j = r)).card)]
  simp_rw [hexact]
  fin_cases i <;> fin_cases s <;>
    simp [pattern, profileMultiplicity, marginalMultiplicity,
      Fin.sum_univ_succ] <;> omega

end MME.StothersFourth.Phi224

theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + 2 * beta + gamma + delta = N) :
    Function.Injective MME.StothersFourth.Phi224.pattern ∧
    (∑ r : Fin 9,
      MME.StothersFourth.Phi224.profileMultiplicity
        alpha beta gamma delta r) = 2 * N ∧
    ∀ w : MME.StothersFourth.Phi224.ProfileWord N,
      (∀ r : Fin 9,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ w j = r)).card =
            MME.StothersFourth.Phi224.profileMultiplicity
              alpha beta gamma delta r) →
      ∀ i : Fin 3, ∀ s : Fin 5,
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦
            MME.StothersFourth.Phi224.modeWord w i j = s)).card =
          MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s := by
  exact ⟨MME.StothersFourth.Phi224.pattern_injective,
    MME.StothersFourth.Phi224.profileMultiplicity_sum
      N alpha beta gamma delta hsum,
    fun w ↦
      MME.StothersFourth.Phi224.exact_profile_implies_marginal_profile
        N alpha beta gamma delta w⟩
