-- Prove2me | solution 1 for mme_stothers_phi224_marginal_fiber_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:26:31.153116+00:00
-- url     : https://prove2.me/submissions/62942f9d-d6db-4992-92ee-becd67415a06

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

/-- Every same-marginal `phi_224` profile is controlled by one off-diagonal
imbalance.  The equations below avoid subtraction and are valid over naturals. -/
theorem marginal_fiber_parameter
    (N alpha beta gamma delta : ℕ) (w : ProfileWord N)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ modeWord w i j = s)).card =
          marginalMultiplicity alpha beta gamma delta i s) :
    let k : Fin 9 → ℕ := fun r ↦
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w j = r)).card
    k 0 = alpha ∧ k 8 = alpha ∧ k 4 = 2 * delta ∧
      k 1 = k 5 ∧ k 3 = k 7 ∧
      k 1 + k 3 = 2 * beta ∧
      k 1 + k 2 = beta + gamma ∧
      k 3 + k 6 = beta + gamma := by
  let k : Fin 9 → ℕ := fun r ↦
    ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ w j = r)).card
  have h00 := hmarginal 0 0
  have h01 := hmarginal 0 1
  have h02 := hmarginal 0 2
  have h10 := hmarginal 1 0
  have h11 := hmarginal 1 1
  have h12 := hmarginal 1 2
  have h20 := hmarginal 2 0
  have h21 := hmarginal 2 1
  have h23 := hmarginal 2 3
  have h24 := hmarginal 2 4
  rw [projectedFiberCard] at h00 h01 h02 h10 h11 h12 h20 h21 h23 h24
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦ pattern r 0) (0 : Fin 5) k] at h00
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦ pattern r 0) (1 : Fin 5) k] at h01
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦ pattern r 0) (2 : Fin 5) k] at h02
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦ pattern r 1) (0 : Fin 5) k] at h10
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦ pattern r 1) (1 : Fin 5) k] at h11
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦ pattern r 1) (2 : Fin 5) k] at h12
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦ pattern r 2) (0 : Fin 5) k] at h20
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦ pattern r 2) (1 : Fin 5) k] at h21
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦ pattern r 2) (3 : Fin 5) k] at h23
  rw [← sum_ite_eq_sum_subtype
      (fun r : Fin 9 ↦ pattern r 2) (4 : Fin 5) k] at h24
  change (∑ r : Fin 9, if pattern r 0 = 0 then k r else 0) =
    alpha + beta + gamma at h00
  change (∑ r : Fin 9, if pattern r 0 = 1 then k r else 0) =
    2 * beta + 2 * delta at h01
  change (∑ r : Fin 9, if pattern r 0 = 2 then k r else 0) =
    alpha + beta + gamma at h02
  change (∑ r : Fin 9, if pattern r 1 = 0 then k r else 0) =
    alpha + beta + gamma at h10
  change (∑ r : Fin 9, if pattern r 1 = 1 then k r else 0) =
    2 * beta + 2 * delta at h11
  change (∑ r : Fin 9, if pattern r 1 = 2 then k r else 0) =
    alpha + beta + gamma at h12
  change (∑ r : Fin 9, if pattern r 2 = 0 then k r else 0) = alpha at h20
  change (∑ r : Fin 9, if pattern r 2 = 1 then k r else 0) = 2 * beta at h21
  change (∑ r : Fin 9, if pattern r 2 = 3 then k r else 0) = 2 * beta at h23
  change (∑ r : Fin 9, if pattern r 2 = 4 then k r else 0) = alpha at h24
  simp [pattern, Fin.sum_univ_succ] at h00 h01 h02 h10 h11 h12 h20 h21 h23 h24
  dsimp only
  change k 0 = alpha ∧ k 8 = alpha ∧ k 4 = 2 * delta ∧
    k 1 = k 5 ∧ k 3 = k 7 ∧ k 1 + k 3 = 2 * beta ∧
    k 1 + k 2 = beta + gamma ∧ k 3 + k 6 = beta + gamma
  omega

end MME.StothersFourth.Phi224

theorem solution
    (N alpha beta gamma delta : ℕ)
    (w : MME.StothersFourth.Phi224.ProfileWord N)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ MME.StothersFourth.Phi224.modeWord w i j = s)).card =
          MME.StothersFourth.Phi224.marginalMultiplicity
            alpha beta gamma delta i s) :
    let k : Fin 9 → ℕ := fun r ↦
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w j = r)).card
    k 0 = alpha ∧ k 8 = alpha ∧ k 4 = 2 * delta ∧
      k 1 = k 5 ∧ k 3 = k 7 ∧
      k 1 + k 3 = 2 * beta ∧
      k 1 + k 2 = beta + gamma ∧
      k 3 + k 6 = beta + gamma := by
  exact MME.StothersFourth.Phi224.marginal_fiber_parameter
    N alpha beta gamma delta w hmarginal
