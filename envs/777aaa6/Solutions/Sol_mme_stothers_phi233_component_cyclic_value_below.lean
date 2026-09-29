-- Prove2me | solution 1 for mme_stothers_phi233_component_cyclic_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:31:28.457102+00:00
-- url     : https://prove2.me/submissions/afa43fef-0637-45b5-b621-77629942bc67

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data
import Theorems.Thm_mme_MMObj_cyclic_tau_value
import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_cyclicSymmetrization_isomorphic_cyclic_orbit
import Theorems.Thm_mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_multiple_extractions_below
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions
import Theorems.Thm_mme_toQ_kronFin

open MME BigOperators Filter

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

private theorem phi233_tau_value_strict_lower
    {K : Type u} [Field K] {T : TensorObj K 3}
    (tau B V : ℝ)
    (hB : 0 < B) (hV : 0 ≤ V) (hVB : V < B)
    (h : HasTauValueAtLeast T tau B) :
    HasTauValueAtLeast T tau V := by
  obtain ⟨e, he, hmultiple⟩ :=
    mme_HasTauValueAtLeast_multiple_extractions_below
      T tau B V hB hV hVB h
  have heOne : 1 ≤ e := he
  have hscale : Tendsto (fun r : ℕ ↦ r * e) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with r hr
    calc
      N ≤ r := hr
      _ = r * 1 := by simp
      _ ≤ r * e := Nat.mul_le_mul_left r heOne
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    T tau V hV (fun r : ℕ ↦ r * e) hscale (fun _ : ℕ ↦ (0 : ℝ))
      tendsto_const_nhds
  filter_upwards with r
  obtain ⟨k, a, b, c, hrestrict, hweight⟩ := hmultiple r
  refine ⟨k, a, b, c, hrestrict, ?_⟩
  simpa using hweight

private theorem phi233_kronFin_two_powers_one_iso
    {K : Type u} [Field K] (A B : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin 2 (fun i ↦
        ((![A, B] : Fin 2 → TensorObj K 3) i).kronPow 1))
      (TensorObj.kron A B) := by
  rw [← TensorQ.toQ_eq_iff]
  rw [mme_toQ_kronFin, TensorQ.toQ_kron]
  simp [Fin.prod_univ_succ, TensorQ.toQ_kronPow]

private theorem phi233_cyclic_kron_two_local
    {K : Type u} [Field K]
    (A B : TensorObj K 3) (tau endpointA endpointB : ℝ)
    (hendpointA : 0 < endpointA) (hendpointB : 0 < endpointB)
    (hA : ∀ V : ℝ, 0 ≤ V → V < endpointA →
      HasTauValueAtLeast (cyclicSymmetrization A) tau V)
    (hB : ∀ V : ℝ, 0 ≤ V → V < endpointB →
      HasTauValueAtLeast (cyclicSymmetrization B) tau V)
    (V : ℝ) (hV : 0 ≤ V) (hVlt : V < endpointA * endpointB) :
    HasTauValueAtLeast
      (cyclicSymmetrization (TensorObj.kron A B)) tau V := by
  let factor : Fin 2 → TensorObj K 3 := ![A, B]
  let endpoint : Fin 2 → ℝ := ![endpointA, endpointB]
  have hproduct : HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kronFin 2
          (fun i ↦ (factor i).kronPow 1))) tau V := by
    apply mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
      factor (fun _ ↦ 1) tau endpoint
    · intro i
      fin_cases i
      · exact hendpointA
      · exact hendpointB
    · intro i W hW hWlt
      fin_cases i
      · exact hA W hW (by simpa [endpoint] using hWlt)
      · exact hB W hW (by simpa [endpoint] using hWlt)
    · exact hV
    · simpa [endpoint, Fin.prod_univ_succ] using hVlt
  have hcyclic : TensorObj.Restrict
      (cyclicSymmetrization
        (TensorObj.kronFin 2 (fun i ↦ (factor i).kronPow 1)))
      (cyclicSymmetrization (TensorObj.kron A B)) :=
    mme_cyclicSymmetrization_mono_restrict
      (by
        simpa only [factor] using
          (phi233_kronFin_two_powers_one_iso A B).1)
  exact mme_HasTauValueAtLeast_mono_restrict hcyclic hproduct

private theorem phi233_component_eight_canonical
    {K : Type u} [Field K] :
    MME.StothersFourth.Phi233.componentObj K 6 (8 : Fin 10) =
      TensorObj.kron
        (TensorObj.permObj cyclicPerm (coupledObj K 6))
        (MMObj K 1 1 38) := by
  unfold MME.StothersFourth.Phi233.componentObj
  rw [show (8 : Fin 10) = (7 : Fin 9).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (7 : Fin 9) = (6 : Fin 8).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (6 : Fin 8) = (5 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (5 : Fin 7) = (4 : Fin 6).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (4 : Fin 6) = (3 : Fin 5).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (3 : Fin 5) = (2 : Fin 4).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (2 : Fin 4) = (1 : Fin 3).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 3) = (0 : Fin 2).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

private theorem phi233_component_eight
    {K : Type u} [Field K] (i : Fin 10) (hi : i.val = 8) :
    MME.StothersFourth.Phi233.componentObj K 6 i =
      TensorObj.kron
        (TensorObj.permObj cyclicPerm (coupledObj K 6))
        (MMObj K 1 1 38) := by
  have hieq : i = (8 : Fin 10) := Fin.ext hi
  rw [hieq]
  exact phi233_component_eight_canonical

private theorem phi233_component_nine_canonical
    {K : Type u} [Field K] :
    MME.StothersFourth.Phi233.componentObj K 6 (9 : Fin 10) =
      MMObj K 1 38 12 := by
  unfold MME.StothersFourth.Phi233.componentObj
  rw [show (9 : Fin 10) = (8 : Fin 9).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (8 : Fin 9) = (7 : Fin 8).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (7 : Fin 8) = (6 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (6 : Fin 7) = (5 : Fin 6).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (5 : Fin 6) = (4 : Fin 5).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (4 : Fin 5) = (3 : Fin 4).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (3 : Fin 4) = (2 : Fin 3).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (2 : Fin 3) = (1 : Fin 2).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

private theorem phi233_component_nine
    {K : Type u} [Field K] (i : Fin 10) (hi : i.val = 9) :
    MME.StothersFourth.Phi233.componentObj K 6 i =
      MMObj K 1 38 12 := by
  have hieq : i = (9 : Fin 10) := Fin.ext hi
  rw [hieq]
  exact phi233_component_nine_canonical

theorem solution
    {K : Type u} [Field K] (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ (r : Fin 10) (V : ℝ),
      0 ≤ V →
      V < (![MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
        MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
        MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
        MME.StothersFourth.E 6 tau ^ (2 : ℕ),
        MME.StothersFourth.L 6 tau ^ (2 : ℕ),
        MME.StothersFourth.L 6 tau ^ (2 : ℕ),
        MME.StothersFourth.E 6 tau ^ (2 : ℕ),
        MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau,
        MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
        MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau] :
          Fin 10 → ℝ) r →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.Phi233.componentObj K 6 r)) tau V := by
  have hE : 0 < MME.StothersFourth.E 6 tau := by
    unfold MME.StothersFourth.E
    positivity
  have hH : 0 < MME.StothersFourth.H 6 tau := by
    unfold MME.StothersFourth.H
    positivity
  have hL : 0 < MME.StothersFourth.L 6 tau := by
    unfold MME.StothersFourth.L
    positivity
  have hEH0 := mme_MMObj_cyclic_tau_value (K := K) 1 38 12 tau
  have hEH2 := mme_MMObj_cyclic_tau_value (K := K) 38 1 12 tau
  have hE2 := mme_MMObj_cyclic_tau_value (K := K) 12 12 1 tau
  have hHbase := mme_MMObj_cyclic_tau_value (K := K) 1 1 38 tau
  have heqEH :
      ((((1 * 38 * 12) * (1 * 38 * 12) * (1 * 38 * 12) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau := by
    unfold MME.StothersFourth.E MME.StothersFourth.H
    norm_num only [Nat.cast_ofNat, Nat.reduceMul, Nat.cast_one]
    rw [show (94818816 : ℝ) = 456 ^ (3 : ℕ) by norm_num]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 456) 3 tau]
    rw [show (456 : ℝ) = 12 * 38 by norm_num]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12)
      (by norm_num : (0 : ℝ) ≤ 38)]
    norm_num
  have heqEH2 :
      ((((38 * 1 * 12) * (38 * 1 * 12) * (38 * 1 * 12) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau := by
    norm_num only [Nat.reduceMul]
    norm_num only [Nat.cast_ofNat] at heqEH ⊢
    exact heqEH
  have heqE2 :
      ((((12 * 12 * 1) * (12 * 12 * 1) * (12 * 12 * 1) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.E 6 tau ^ (2 : ℕ) := by
    unfold MME.StothersFourth.E
    norm_num only [Nat.cast_ofNat, Nat.reduceMul, Nat.cast_one]
    rw [show (2985984 : ℝ) = 12 ^ (6 : ℕ) by norm_num]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 12) 6 tau]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 12)
      (3 * tau) 2]
    congr 1
    ring
  have heqH :
      ((((1 * 1 * 38) * (1 * 1 * 38) * (1 * 1 * 38) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.H 6 tau := by
    unfold MME.StothersFourth.H
    norm_num only [Nat.cast_ofNat, Nat.reduceMul, Nat.cast_one]
    rw [show (54872 : ℝ) = 38 ^ (3 : ℕ) by norm_num]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 38) 3 tau]
    norm_num
  have hEH0' : HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 1 38 12)) tau
      (MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau) :=
    heqEH ▸ hEH0
  have hEH2' : HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 38 1 12)) tau
      (MME.StothersFourth.E 6 tau * MME.StothersFourth.H 6 tau) :=
    heqEH2 ▸ hEH2
  have hE2' : HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 12 12 1)) tau
      (MME.StothersFourth.E 6 tau ^ (2 : ℕ)) :=
    heqE2 ▸ hE2
  have hHbase' : HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 1 1 38)) tau
      (MME.StothersFourth.H 6 tau) := heqH ▸ hHbase
  have hMMH : ∀ W : ℝ, 0 ≤ W → W < MME.StothersFourth.H 6 tau →
      HasTauValueAtLeast (cyclicSymmetrization (MMObj K 1 1 38)) tau W := by
    intro W hW hWlt
    exact phi233_tau_value_strict_lower tau _ W hH hW hWlt hHbase'
  have hCoupled : ∀ W : ℝ, 0 ≤ W → W < MME.StothersFourth.L 6 tau →
      HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau W := by
    intro W hW hWlt
    exact mme_CW_q6_coupled_raw_cyclic_value_below
      (K := K) tau htau W hW (by simpa only [MME.StothersFourth.L] using hWlt)
  have hCoupledCyclic : ∀ W : ℝ, 0 ≤ W → W < MME.StothersFourth.L 6 tau →
      HasTauValueAtLeast
        (cyclicSymmetrization (TensorObj.permObj cyclicPerm (coupledObj K 6)))
        tau W := by
    intro W hW hWlt
    exact mme_HasTauValueAtLeast_mono_restrict
      (mme_cyclicSymmetrization_isomorphic_cyclic_orbit
        (coupledObj K 6)).1.2
      (hCoupled W hW hWlt)
  have hCoupledCyclicSq : ∀ W : ℝ, 0 ≤ W → W < MME.StothersFourth.L 6 tau →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)))
        tau W := by
    intro W hW hWlt
    exact mme_HasTauValueAtLeast_mono_restrict
      (mme_cyclicSymmetrization_isomorphic_cyclic_orbit
        (coupledObj K 6)).2.2
      (hCoupled W hW hWlt)
  intro r V hV hVlt
  fin_cases r
  all_goals simp only [] at hVlt ⊢
  · change V < MME.StothersFourth.E 6 tau *
      MME.StothersFourth.H 6 tau at hVlt
    change HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 1 38 12)) tau V
    exact phi233_tau_value_strict_lower tau _ V (mul_pos hE hH)
      hV hVlt hEH0'
  · change V < MME.StothersFourth.H 6 tau *
      MME.StothersFourth.L 6 tau at hVlt
    change HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kron (MMObj K 1 1 38)
          (TensorObj.permObj cyclicPerm (coupledObj K 6)))) tau V
    exact phi233_cyclic_kron_two_local
      (MMObj K 1 1 38)
      (TensorObj.permObj cyclicPerm (coupledObj K 6))
      tau (MME.StothersFourth.H 6 tau) (MME.StothersFourth.L 6 tau)
      hH hL hMMH hCoupledCyclic V hV hVlt
  · change V < MME.StothersFourth.E 6 tau *
      MME.StothersFourth.H 6 tau at hVlt
    change HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 38 1 12)) tau V
    exact phi233_tau_value_strict_lower tau _ V (mul_pos hE hH)
      hV hVlt hEH2'
  · change V < MME.StothersFourth.E 6 tau ^ (2 : ℕ) at hVlt
    change HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 12 12 1)) tau V
    exact phi233_tau_value_strict_lower tau _ V (pow_pos hE 2)
      hV hVlt hE2'
  · change V < MME.StothersFourth.L 6 tau ^ (2 : ℕ) at hVlt
    change HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kron (coupledObj K 6)
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)))) tau V
    exact phi233_cyclic_kron_two_local
      (coupledObj K 6)
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6))
      tau (MME.StothersFourth.L 6 tau) (MME.StothersFourth.L 6 tau)
      hL hL hCoupled hCoupledCyclicSq V hV (by
        simpa [pow_two] using hVlt)
  · change V < MME.StothersFourth.L 6 tau ^ (2 : ℕ) at hVlt
    change HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kron
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6))
          (coupledObj K 6))) tau V
    exact phi233_cyclic_kron_two_local
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6))
      (coupledObj K 6)
      tau (MME.StothersFourth.L 6 tau) (MME.StothersFourth.L 6 tau)
      hL hL hCoupledCyclicSq hCoupled V hV (by
        simpa [pow_two] using hVlt)
  · change V < MME.StothersFourth.E 6 tau ^ (2 : ℕ) at hVlt
    change HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 12 12 1)) tau V
    exact phi233_tau_value_strict_lower tau _ V (pow_pos hE 2)
      hV hVlt hE2'
  · change V < MME.StothersFourth.E 6 tau *
      MME.StothersFourth.H 6 tau at hVlt
    change HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 38 1 12)) tau V
    exact phi233_tau_value_strict_lower tau _ V (mul_pos hE hH)
      hV hVlt hEH2'
  · change V < MME.StothersFourth.H 6 tau *
      MME.StothersFourth.L 6 tau at hVlt
    rw [phi233_component_eight _ (by rfl)]
    exact phi233_cyclic_kron_two_local
      (TensorObj.permObj cyclicPerm (coupledObj K 6))
      (MMObj K 1 1 38)
      tau (MME.StothersFourth.L 6 tau) (MME.StothersFourth.H 6 tau)
      hL hH hCoupledCyclic hMMH V hV (by
        simpa [mul_comm] using hVlt)
  · change V < MME.StothersFourth.E 6 tau *
      MME.StothersFourth.H 6 tau at hVlt
    rw [phi233_component_nine _ (by rfl)]
    exact phi233_tau_value_strict_lower tau _ V (mul_pos hE hH)
      hV hVlt hEH0'
