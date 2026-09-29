-- Prove2me | solution 1 for mme_complete_split_112_zero_profile_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:11:15.983866+00:00
-- url     : https://prove2.me/submissions/09f8e3d8-7e81-4cf9-bece-ae60b53021af

import Definitions.Def_mme_CW_q6_primary_hash_family
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open MME

private abbrev BalancedSet (N : ℕ) :=
  {s : Finset (Fin (2 * N)) // s.card = N}

private def balancedAddress {N : ℕ} (s : BalancedSet N) :
    CWQ6CoupledAddress N :=
  fun i j => ![if j ∈ s.1 then 0 else 1,
    if j ∈ s.1 then 1 else 0, 2] i

private theorem balancedAddress_exact {N : ℕ} (s : BalancedSet N) :
    CWQ6CoupledCoordinatewiseSupported (balancedAddress s) ∧
      ∀ i r : Fin 3,
        (Finset.univ.filter (fun j => balancedAddress s i j = r)).card =
          cwQ6CoupledMarginalMultiplicity N 0 N i r := by
  constructor
  · intro j
    by_cases hj : j ∈ s.1 <;>
      simp [balancedAddress, hj]
  · have hs : (Finset.univ.filter (fun j => j ∈ s.1)) = s.1 := by
      ext j
      simp
    have hc : (Finset.univ.filter (fun j => j ∉ s.1)) = s.1ᶜ := by
      ext j
      simp
    have hcard : s.1ᶜ.card = N := by
      rw [Finset.card_compl, s.2]
      simp only [Fintype.card_fin]
      omega
    intro i r
    fin_cases i <;> fin_cases r <;>
      simp [balancedAddress, cwQ6CoupledMarginalMultiplicity, hs, hc, hcard, s.2]
    all_goals intro x; split_ifs <;> decide

private def balancedExact {N : ℕ} (s : BalancedSet N) :
    CWQ6ExactCoupledAddress N 0 N :=
  ⟨balancedAddress s, balancedAddress_exact s⟩

private theorem balanced_x_injective {N : ℕ} :
    Function.Injective (fun s : BalancedSet N => balancedAddress s 0) := by
  intro s t h
  apply Subtype.ext
  ext j
  have hj := congrFun h j
  by_cases hs : j ∈ s.1 <;> by_cases ht : j ∈ t.1 <;>
    simp_all [balancedAddress]

private theorem balanced_y_injective {N : ℕ} :
    Function.Injective (fun s : BalancedSet N => balancedAddress s 1) := by
  intro s t h
  apply Subtype.ext
  ext j
  have hj := congrFun h j
  by_cases hs : j ∈ s.1 <;> by_cases ht : j ∈ t.1 <;>
    simp_all [balancedAddress]

private theorem balanced_mixed {N : ℕ} (s t u : BalancedSet N)
    (h : CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress (balancedAddress s) (balancedAddress t)
        (balancedAddress u))) : s = t := by
  apply balanced_x_injective
  funext j
  have hj := h j
  by_cases hs : j ∈ s.1 <;> by_cases ht : j ∈ t.1 <;>
    simp_all [balancedAddress, cwQ6CoupledMixedAddress]

private noncomputable def balancedIndex (N : ℕ) :
    Fin (Nat.choose (2 * N) N) ≃ BalancedSet N :=
  (Fintype.equivFinOfCardEq (by
    simp only [BalancedSet, Fintype.card_finset_len, Fintype.card_fin])).symm

private theorem balanced_family (N : ℕ) :
    Nonempty (CWQ6PrimaryHashFamily N 0 N 1 (Nat.choose (2 * N) N)) := by
  classical
  refine ⟨{
    hHpos := Nat.choose_pos (by omega)
    entry := fun p => balancedExact (balancedIndex N p.2)
    xInjective := ?_
    yInjective := ?_
    zSameFiber := ?_
    zSeparatesFibers := ?_
    induced := ?_ }⟩
  · intro p q h
    apply Prod.ext (Subsingleton.elim _ _)
    apply (balancedIndex N).injective
    exact balanced_x_injective h
  · intro p q h
    apply Prod.ext (Subsingleton.elim _ _)
    apply (balancedIndex N).injective
    exact balanced_y_injective h
  · intros
    rfl
  · intros
    exact Subsingleton.elim _ _
  · intro p q r h
    refine ⟨?_, Subsingleton.elim _ _⟩
    apply Prod.ext (Subsingleton.elim _ _)
    apply (balancedIndex N).injective
    exact balanced_mixed _ _ _ h

theorem solution (N : ℕ) :
    Nonempty (CWQ6PrimaryHashFamily N 0 N 1 (Nat.choose (2 * N) N)) ∧
      Nat.choose (2 * N) N ≤ 4 ^ N := by
  refine ⟨balanced_family N, ?_⟩
  calc
    Nat.choose (2 * N) N ≤ 2 ^ (2 * N) := Nat.choose_le_two_pow _ _
    _ = 4 ^ N := by rw [pow_mul]; norm_num
