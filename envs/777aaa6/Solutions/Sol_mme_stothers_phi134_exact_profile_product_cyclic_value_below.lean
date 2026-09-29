-- Prove2me | solution 1 for mme_stothers_phi134_exact_profile_product_cyclic_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:35:55.319959+00:00
-- url     : https://prove2.me/submissions/99e23843-1b30-4825-ac63-94c985fbad8c

import Mathlib.Tactic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_stothers_phi134_profile_data
import Theorems.Thm_mme_CW_q6_coupled_raw_cyclic_value_below
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Theorems.Thm_mme_MMObj_cyclic_tau_value
import Theorems.Thm_mme_cyclicSymmetrization_isomorphic_cyclic_orbit
import Theorems.Thm_mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
import Theorems.Thm_mme_cyclic_kron_two_strict_below_product

open MME BigOperators Filter
open MME.StothersFourth.Phi134

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

private theorem component_zero_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (0 : Fin 8) = MMObj K 1 12 1 := by
  unfold componentObj
  rw [Matrix.cons_val_zero]

private theorem component_one_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (1 : Fin 8) =
      TensorObj.kron (MMObj K 1 1 12)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)) := by
  unfold componentObj
  rw [show (1 : Fin 8) = (0 : Fin 7).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]

private theorem component_two_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (2 : Fin 8) =
      TensorObj.kron (MMObj K 1 1 38) (coupledObj K 6) := by
  unfold componentObj
  rw [show (2 : Fin 8) = (1 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 7) = (0 : Fin 6).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

private theorem component_three_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (3 : Fin 8) = MMObj K 12 1 12 := by
  unfold componentObj
  rw [show (3 : Fin 8) = (2 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (2 : Fin 7) = (1 : Fin 6).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 6) = (0 : Fin 5).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]

private theorem component_four_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (4 : Fin 8) = MMObj K 12 1 12 := by
  unfold componentObj
  rw [show (4 : Fin 8) = (3 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (3 : Fin 7) = (2 : Fin 6).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (2 : Fin 6) = (1 : Fin 5).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 5) = (0 : Fin 4).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]

private theorem component_five_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (5 : Fin 8) =
      TensorObj.kron (coupledObj K 6) (MMObj K 1 1 38) := by
  unfold componentObj
  rw [show (5 : Fin 8) = (4 : Fin 7).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (4 : Fin 7) = (3 : Fin 6).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (3 : Fin 6) = (2 : Fin 5).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (2 : Fin 5) = (1 : Fin 4).succ by rfl,
    Matrix.cons_val_succ]
  rw [show (1 : Fin 4) = (0 : Fin 3).succ by rfl,
    Matrix.cons_val_succ, Matrix.cons_val_zero]
  norm_num

private theorem component_six_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (6 : Fin 8) =
      TensorObj.kron
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6))
        (MMObj K 1 1 12) := by
  unfold componentObj
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

private theorem component_seven_canonical
    {K : Type u} [Field K] :
    componentObj K 6 (7 : Fin 8) = MMObj K 1 12 1 := by
  unfold componentObj
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

private theorem value_downward {K : Type u} [Field K]
    (T : TensorObj K 3) (tau B V : ℝ)
    (h : HasTauValueAtLeast T tau B)
    (hV : 0 ≤ V) (hVB : V ≤ B) :
    HasTauValueAtLeast T tau V := by
  refine ⟨hV, ?_⟩
  intro eps heps
  apply (h.2 eps heps).mono
  rintro N ⟨k, a, b, c, hr, hbound⟩
  refine ⟨k, a, b, c, hr, ?_⟩
  by_cases heps1 : eps ≤ 1
  · exact (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hV hVB _) (by linarith)).trans hbound
  · exact (mul_nonpos_of_nonneg_of_nonpos
      (pow_nonneg hV _) (by linarith)).trans
        (Finset.sum_nonneg (fun _ _ ↦
          Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Strict cyclic tau-value endpoints of the eight `phi_134` fine payloads,
in the source order 004, 013, 022, 031, 103, 112, 121, 130. -/
noncomputable def phi134Endpoint (tau : ℝ) : Fin 8 → ℝ :=
  ![MME.StothersFourth.E 6 tau,
    MME.StothersFourth.E 6 tau * MME.StothersFourth.L 6 tau,
    MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau,
    MME.StothersFourth.E 6 tau ^ (2 : ℕ),
    MME.StothersFourth.E 6 tau ^ (2 : ℕ),
    MME.StothersFourth.L 6 tau * MME.StothersFourth.H 6 tau,
    MME.StothersFourth.L 6 tau * MME.StothersFourth.E 6 tau,
    MME.StothersFourth.E 6 tau]

private theorem endpoint_pos (tau : ℝ) (r : Fin 8) :
    0 < phi134Endpoint tau r := by
  fin_cases r <;>
    simp [phi134Endpoint, MME.StothersFourth.L,
      MME.StothersFourth.E, MME.StothersFourth.H] <;>
    positivity

private theorem mmE_value {K : Type u} [Field K]
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.E 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 1 1 12)) tau V := by
  have he :
      ((((1 * 1 * 12) * (1 * 1 * 12) * (1 * 1 * 12) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.E 6 tau := by
    norm_num [MME.StothersFourth.E]
    rw [show (1728 : ℝ) = 12 ^ (3 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 12) 3 tau]
    norm_num
  exact value_downward _ _ _ _
    (he ▸ mme_MMObj_cyclic_tau_value (K := K) 1 1 12 tau) hV hVB.le

private theorem mmEmid_value {K : Type u} [Field K]
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.E 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 1 12 1)) tau V := by
  have he :
      ((((1 * 12 * 1) * (1 * 12 * 1) * (1 * 12 * 1) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.E 6 tau := by
    norm_num [MME.StothersFourth.E]
    rw [show (1728 : ℝ) = 12 ^ (3 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 12) 3 tau]
    norm_num
  exact value_downward _ _ _ _
    (he ▸ mme_MMObj_cyclic_tau_value (K := K) 1 12 1 tau) hV hVB.le

private theorem mmH_value {K : Type u} [Field K]
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.H 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 1 1 38)) tau V := by
  have he :
      ((((1 * 1 * 38) * (1 * 1 * 38) * (1 * 1 * 38) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.H 6 tau := by
    norm_num [MME.StothersFourth.H]
    rw [show (54872 : ℝ) = 38 ^ (3 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 38) 3 tau]
    norm_num
  exact value_downward _ _ _ _
    (he ▸ mme_MMObj_cyclic_tau_value (K := K) 1 1 38 tau) hV hVB.le

private theorem mmE2_value {K : Type u} [Field K]
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.E 6 tau ^ (2 : ℕ)) :
    HasTauValueAtLeast
      (cyclicSymmetrization (MMObj K 12 1 12)) tau V := by
  have he :
      ((((12 * 1 * 12) * (12 * 1 * 12) * (12 * 1 * 12) : ℕ) : ℝ) ^ tau) =
        MME.StothersFourth.E 6 tau ^ (2 : ℕ) := by
    norm_num [MME.StothersFourth.E]
    rw [show (2985984 : ℝ) = 12 ^ (6 : ℕ) by norm_num,
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 12) 6 tau]
    calc
      (12 : ℝ) ^ ((6 : ℝ) * tau) =
          (12 : ℝ) ^ ((3 * tau) * 2) := by congr 1; ring
      _ = ((12 : ℝ) ^ (3 * tau)) ^ (2 : ℝ) :=
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 12) _ _
      _ = ((12 : ℝ) ^ (3 * tau)) ^ (2 : ℕ) := Real.rpow_two _
  exact value_downward _ _ _ _
    (he ▸ mme_MMObj_cyclic_tau_value (K := K) 12 1 12 tau) hV hVB.le

private theorem coupled_value {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.L 6 tau) :
    HasTauValueAtLeast (cyclicSymmetrization (coupledObj K 6)) tau V :=
  mme_CW_q6_coupled_raw_cyclic_value_below tau htau V hV hVB

private theorem rotated_coupled_value {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.L 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6))) tau V :=
  mme_HasTauValueAtLeast_mono_restrict
    (mme_cyclicSymmetrization_isomorphic_cyclic_orbit
      (coupledObj K 6)).2.2
    (coupled_value tau htau V hV hVB)

private theorem componentEL_left {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.E 6 tau * MME.StothersFourth.L 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kron (MMObj K 1 1 12)
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K 6)))) tau V := by
  apply mme_cyclic_kron_two_strict_below_product
    (MMObj K 1 1 12)
    (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6))
    tau (MME.StothersFourth.E 6 tau) (MME.StothersFourth.L 6 tau)
    (by unfold MME.StothersFourth.E; positivity)
    (by unfold MME.StothersFourth.L; positivity)
    (mmE_value tau) (rotated_coupled_value tau htau) V hV hVB

private theorem componentHL_left {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.H 6 tau * MME.StothersFourth.L 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kron (MMObj K 1 1 38) (coupledObj K 6))) tau V := by
  apply mme_cyclic_kron_two_strict_below_product
    (MMObj K 1 1 38) (coupledObj K 6)
    tau (MME.StothersFourth.H 6 tau) (MME.StothersFourth.L 6 tau)
    (by unfold MME.StothersFourth.H; positivity)
    (by unfold MME.StothersFourth.L; positivity)
    (mmH_value tau) (coupled_value tau htau) V hV hVB

private theorem componentLH_right {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.L 6 tau * MME.StothersFourth.H 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kron (coupledObj K 6) (MMObj K 1 1 38))) tau V := by
  apply mme_cyclic_kron_two_strict_below_product
    (coupledObj K 6) (MMObj K 1 1 38)
    tau (MME.StothersFourth.L 6 tau) (MME.StothersFourth.H 6 tau)
    (by unfold MME.StothersFourth.L; positivity)
    (by unfold MME.StothersFourth.H; positivity)
    (coupled_value tau htau) (mmH_value tau) V hV hVB

private theorem componentLE_right {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < MME.StothersFourth.L 6 tau * MME.StothersFourth.E 6 tau) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kron
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6))
          (MMObj K 1 1 12))) tau V := by
  apply mme_cyclic_kron_two_strict_below_product
    (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6))
    (MMObj K 1 1 12)
    tau (MME.StothersFourth.L 6 tau) (MME.StothersFourth.E 6 tau)
    (by unfold MME.StothersFourth.L; positivity)
    (by unfold MME.StothersFourth.E; positivity)
    (rotated_coupled_value tau htau) (mmE_value tau) V hV hVB

private theorem component_value {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (r : Fin 8) (V : ℝ) (hV : 0 ≤ V)
    (hVB : V < phi134Endpoint tau r) :
    HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 r)) tau V := by
  fin_cases r <;> simp only at hVB ⊢
  · change V < phi134Endpoint tau (0 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (0 : Fin 8))) tau V
    rw [component_zero_canonical]
    exact mmEmid_value (K := K) tau V hV
      (by simpa only [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (1 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (1 : Fin 8))) tau V
    rw [component_one_canonical]
    exact componentEL_left (K := K) tau htau V hV
      (by simpa only [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (2 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (2 : Fin 8))) tau V
    rw [component_two_canonical]
    exact componentHL_left (K := K) tau htau V hV
      (by simpa only [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (3 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (3 : Fin 8))) tau V
    rw [component_three_canonical]
    exact mmE2_value (K := K) tau V hV
      (by simpa only [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (4 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (4 : Fin 8))) tau V
    rw [component_four_canonical]
    exact mmE2_value (K := K) tau V hV
      (by simpa only [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (5 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (5 : Fin 8))) tau V
    rw [component_five_canonical]
    exact componentLH_right (K := K) tau htau V hV
      (by simpa only [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (6 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (6 : Fin 8))) tau V
    rw [component_six_canonical]
    exact componentLE_right (K := K) tau htau V hV
      (by simpa only [phi134Endpoint] using hVB)
  · change V < phi134Endpoint tau (7 : Fin 8) at hVB
    change HasTauValueAtLeast
      (cyclicSymmetrization (componentObj K 6 (7 : Fin 8))) tau V
    rw [component_seven_canonical]
    exact mmEmid_value (K := K) tau V hV
      (by simpa only [phi134Endpoint] using hVB)

/-- Every exact symmetric `phi_134` profile block attains the product of its
eight component endpoints. -/
theorem solution {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (alpha beta gamma delta : ℕ)
    (W : ℝ) (hW : 0 ≤ W)
    (hWB :
      W <
        MME.StothersFourth.L 6 tau ^ (2 * beta + 2 * gamma) *
        MME.StothersFourth.E 6 tau ^
          (2 * alpha + 2 * beta + 4 * delta) *
        MME.StothersFourth.H 6 tau ^ (2 * gamma)) :
    HasTauValueAtLeast
      (cyclicSymmetrization
        (TensorObj.kronFin 8 (fun r ↦
          (componentObj K 6 r).kronPow
            (profileMultiplicity alpha beta gamma delta r)))) tau W := by
  apply mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
    (componentObj K 6)
    (profileMultiplicity alpha beta gamma delta)
    tau (phi134Endpoint tau) (endpoint_pos tau)
    (component_value tau htau) W hW
  convert hWB using 1
  simp [Fin.prod_univ_succ, Fin.succ, phi134Endpoint,
    profileMultiplicity, mul_pow, pow_add, pow_mul]
  ring
