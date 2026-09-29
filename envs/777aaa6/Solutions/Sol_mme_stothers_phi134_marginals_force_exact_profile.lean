-- Prove2me | solution 1 for mme_stothers_phi134_marginals_force_exact_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:50:00.506733+00:00
-- url     : https://prove2.me/submissions/eb4d2148-00e8-4b70-9dfb-a9b4239ae3f9

import Definitions.Def_mme_stothers_phi134_profile_data

open BigOperators

namespace MME.StothersFourth.Phi134

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option warningAsError true

private theorem pattern_injective : Function.Injective pattern := by
  intro r s h
  have h0 := congrFun h (0 : Fin 3)
  have h1 := congrFun h (1 : Fin 3)
  have h2 := congrFun h (2 : Fin 3)
  fin_cases r <;> fin_cases s <;>
    simp [pattern, MME.cwSquareBlockType] at h0 h1 h2 ⊢

private noncomputable def coordinateClass
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) : Fin 8 :=
  Classical.choose (hx j)

private theorem coordinateClass_spec
    {N : ℕ} (x : ProfileAddress N) (hx : CoordinatewiseSupported x)
    (j : Fin (2 * N)) :
    addressType x j = pattern (coordinateClass x hx j) :=
  Classical.choose_spec (hx j)

private theorem projectedFiberCard
    {N : ℕ} (w : Fin (2 * N) → Fin 8) (i : Fin 3) (s : Fin 5) :
    ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ pattern (w j) i = s)).card =
      ∑ r : {r : Fin 8 // pattern r i = s},
        ((Finset.univ : Finset (Fin (2 * N))).filter
          (fun j ↦ w j = r.1)).card := by
  classical
  let e :
      {j : Fin (2 * N) // pattern (w j) i = s} ≃
        Sigma fun r : {r : Fin 8 // pattern r i = s} ↦
          {j : Fin (2 * N) // w j = r.1} := {
    toFun j := ⟨⟨w j.1, j.2⟩, ⟨j.1, rfl⟩⟩
    invFun x := ⟨x.2.1, by
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
  intro r _hr
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

private theorem label_counts_of_marginals
    (N alpha beta gamma delta : ℕ)
    (w : Fin (2 * N) → Fin 8)
    (hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ pattern (w j) i = s)).card =
          marginalMultiplicity N alpha beta gamma delta i s) :
    ∀ r : Fin 8,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ w j = r)).card =
          profileMultiplicity alpha beta gamma delta r := by
  let k : Fin 8 → ℕ := fun r ↦
    ((Finset.univ : Finset (Fin (2 * N))).filter
      (fun j ↦ w j = r)).card
  have h24 := hmarginal 2 4
  have h20 := hmarginal 2 0
  have h10 := hmarginal 1 0
  have h13 := hmarginal 1 3
  have h23 := hmarginal 2 3
  have h21 := hmarginal 2 1
  have h11 := hmarginal 1 1
  have h12 := hmarginal 1 2
  rw [projectedFiberCard, ← sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 2) (4 : Fin 5) k] at h24
  rw [projectedFiberCard, ← sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 2) (0 : Fin 5) k] at h20
  rw [projectedFiberCard, ← sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 1) (0 : Fin 5) k] at h10
  rw [projectedFiberCard, ← sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 1) (3 : Fin 5) k] at h13
  rw [projectedFiberCard, ← sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 2) (3 : Fin 5) k] at h23
  rw [projectedFiberCard, ← sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 2) (1 : Fin 5) k] at h21
  rw [projectedFiberCard, ← sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 1) (1 : Fin 5) k] at h11
  rw [projectedFiberCard, ← sum_ite_eq_sum_subtype
      (fun r : Fin 8 ↦ pattern r 1) (2 : Fin 5) k] at h12
  change (∑ r : Fin 8, if pattern r 2 = 4 then k r else 0) = alpha at h24
  change (∑ r : Fin 8, if pattern r 2 = 0 then k r else 0) = alpha at h20
  change (∑ r : Fin 8, if pattern r 1 = 0 then k r else 0) =
    alpha + delta at h10
  change (∑ r : Fin 8, if pattern r 1 = 3 then k r else 0) =
    alpha + delta at h13
  change (∑ r : Fin 8, if pattern r 2 = 3 then k r else 0) =
    beta + delta at h23
  change (∑ r : Fin 8, if pattern r 2 = 1 then k r else 0) =
    beta + delta at h21
  change (∑ r : Fin 8, if pattern r 1 = 1 then k r else 0) =
    beta + gamma at h11
  change (∑ r : Fin 8, if pattern r 1 = 2 then k r else 0) =
    beta + gamma at h12
  simp [pattern, MME.cwSquareBlockType, Fin.sum_univ_succ] at h24 h20 h10 h13 h23 h21 h11 h12
  intro r
  change k r = profileMultiplicity alpha beta gamma delta r
  fin_cases r <;> simp [profileMultiplicity] <;> omega

end MME.StothersFourth.Phi134

theorem solution
    (N alpha beta gamma delta : ℕ)
    (x : MME.StothersFourth.Phi134.MarginalAddress
      N alpha beta gamma delta) :
    ∀ r : Fin 8,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦
          MME.StothersFourth.Phi134.addressType x.1 j =
            MME.StothersFourth.Phi134.pattern r)).card =
        MME.StothersFourth.Phi134.profileMultiplicity
          alpha beta gamma delta r := by
  classical
  let w : Fin (2 * N) → Fin 8 :=
    MME.StothersFourth.Phi134.coordinateClass x.1 x.2.1
  have htype (j : Fin (2 * N)) :
      MME.StothersFourth.Phi134.addressType x.1 j =
        MME.StothersFourth.Phi134.pattern (w j) := by
    exact MME.StothersFourth.Phi134.coordinateClass_spec x.1 x.2.1 j
  have hmarginal : ∀ i : Fin 3, ∀ s : Fin 5,
      ((Finset.univ : Finset (Fin (2 * N))).filter
        (fun j ↦ MME.StothersFourth.Phi134.pattern (w j) i = s)).card =
          MME.StothersFourth.Phi134.marginalMultiplicity
            N alpha beta gamma delta i s := by
    intro i s
    rw [← x.2.2 i s]
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hij := congrFun (htype j) i
    change x.1 i j = MME.StothersFourth.Phi134.pattern (w j) i at hij
    exact ⟨fun h ↦ hij.trans h, fun h ↦ hij.symm.trans h⟩
  have hcounts :=
    MME.StothersFourth.Phi134.label_counts_of_marginals
      N alpha beta gamma delta w hmarginal
  intro r
  rw [← hcounts r]
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    apply MME.StothersFourth.Phi134.pattern_injective
    exact (htype j).symm.trans h
  · intro h
    exact (htype j).trans (congrArg MME.StothersFourth.Phi134.pattern h)
