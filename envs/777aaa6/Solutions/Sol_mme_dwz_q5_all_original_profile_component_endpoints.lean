-- Prove2me | solution 1 for mme_dwz_q5_all_original_profile_component_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T18:11:19.611709+00:00
-- url     : https://prove2.me/submissions/dc0e12f6-83c3-4a0c-aafc-11f82da9029e

import Theorems.Thm_mme_dwz_q5_fourth_boundary_original_profile_endpoints
import Theorems.Thm_mme_dwz_positive_422_original_profile_value_at_ledger_rate
import Theorems.Thm_mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
import Theorems.Thm_mme_dwz_positive_332_original_profile_value
import Theorems.Thm_mme_dwz_positive_323_original_profile_value
import Theorems.Thm_mme_dwz_positive_125_original_profile_value_at_ledger_rate
import Theorems.Thm_mme_dwz_positive_233_original_profile_value
import Theorems.Thm_mme_dwz_positive_242_original_profile_value
import Theorems.Thm_mme_dwz_positive_224_original_profile_value
import Theorems.Thm_mme_dwz_positive_251_original_profile_value_at_ledger_rate
import Theorems.Thm_mme_dwz_positive_431_original_profile_value
import Theorems.Thm_mme_dwz_positive_521_original_profile_value_at_ledger_rate
import Theorems.Thm_mme_dwz_positive_341_original_profile_value
import Theorems.Thm_mme_dwz_positive_215_original_profile_value_at_ledger_rate
import Theorems.Thm_mme_dwz_positive_512_original_profile_value_at_ledger_rate
import Theorems.Thm_mme_dwz_positive_152_original_profile_value_at_ledger_rate
import Theorems.Thm_mme_dwz_positive_143_original_profile_value
import Theorems.Thm_mme_dwz_positive_314_original_profile_value
import Theorems.Thm_mme_dwz_positive_413_original_profile_value
import Theorems.Thm_mme_dwz_positive_134_original_profile_value
import Theorems.Thm_mme_dwz_positive_611_original_profile_value
import Theorems.Thm_mme_dwz_positive_161_original_profile_value
import Theorems.Thm_mme_dwz_positive_116_original_profile_value
import Definitions.Def_mme_dwz_q5_global_component_ledger_data
import Mathlib.Tactic
open MME.DWZQ5GlobalLedger MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
universe u
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem component_11 {K : Type u} [Field K] : ComponentEndpoint K 11 := by
  have hrQ : componentLogFloor 11 = (1364339668593 / 250000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 11 : ℝ) = 1364339668593 / 250000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 11) MME.DWZPositiveComponent125.parentProfile 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_125_original_profile_value_at_ledger_rate (K := K))

theorem component_20 {K : Type u} [Field K] : ComponentEndpoint K 20 := by
  have hrQ : componentLogFloor 20 = (6676015030321 / 1000000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 20 : ℝ) = 6676015030321 / 1000000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 20) MME.DWZPositiveComponent233.parentProfile 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_233_original_profile_value (K := K))

theorem component_21 {K : Type u} [Field K] : ComponentEndpoint K 21 := by
  have hrQ : componentLogFloor 21 = (3202624344287 / 500000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 21 : ℝ) = 3202624344287 / 500000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 21) MME.DWZPositiveComponent242.parentProfile 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_242_original_profile_value (K := K))

theorem component_19 {K : Type u} [Field K] : ComponentEndpoint K 19 := by
  have hrQ : componentLogFloor 19 = (6404755418211 / 1000000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 19 : ℝ) = 6404755418211 / 1000000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 19) MME.DWZPositiveComponent224.parentProfile 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_224_original_profile_value (K := K))

theorem component_22 {K : Type u} [Field K] : ComponentEndpoint K 22 := by
  have hrQ : componentLogFloor 22 = (2730192919793 / 500000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 22 : ℝ) = 2730192919793 / 500000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 22) MME.DWZPositiveComponent251.parentProfile 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_251_original_profile_value_at_ledger_rate (K := K))

theorem component_33 {K : Type u} [Field K] : ComponentEndpoint K 33 := by
  have hrQ : componentLogFloor 33 = (3079765900131 / 500000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 33 : ℝ) = 3079765900131 / 500000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 33) MME.DWZPositiveComponent431.parentProfile 7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_431_original_profile_value (K := K))

theorem component_37 {K : Type u} [Field K] : ComponentEndpoint K 37 := by
  have hrQ : componentLogFloor 37 = (5460385998309 / 1000000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 37 : ℝ) = 5460385998309 / 1000000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 37) MME.DWZPositiveComponent521.parentProfile 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_521_original_profile_value_at_ledger_rate (K := K))

theorem component_28 {K : Type u} [Field K] : ComponentEndpoint K 28 := by
  have hrQ : componentLogFloor 28 = (6159531789539 / 1000000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 28 : ℝ) = 6159531789539 / 1000000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 28) MME.DWZPositiveComponent341.parentProfile 320
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_341_original_profile_value (K := K))

theorem component_18 {K : Type u} [Field K] : ComponentEndpoint K 18 := by
  have hrQ : componentLogFloor 18 = (5457358688867 / 1000000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 18 : ℝ) = 5457358688867 / 1000000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 18) MME.DWZPositiveComponent215.parentProfile 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_215_original_profile_value_at_ledger_rate (K := K))

theorem component_36 {K : Type u} [Field K] : ComponentEndpoint K 36 := by
  have hrQ : componentLogFloor 36 = (2730192631343 / 500000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 36 : ℝ) = 2730192631343 / 500000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 36) MME.DWZPositiveComponent512.parentProfile 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_512_original_profile_value_at_ledger_rate (K := K))

theorem component_14 {K : Type u} [Field K] : ComponentEndpoint K 14 := by
  have hrQ : componentLogFloor 14 = (682548175351 / 125000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 14 : ℝ) = 682548175351 / 125000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 14) MME.DWZPositiveComponent152.parentProfile 12
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_152_original_profile_value_at_ledger_rate (K := K))

theorem component_13 {K : Type u} [Field K] : ComponentEndpoint K 13 := by
  have hrQ : componentLogFloor 13 = (615953393593 / 100000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 13 : ℝ) = 615953393593 / 100000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 13) MME.DWZPositiveComponent143.parentProfile 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_143_original_profile_value (K := K))

theorem component_25 {K : Type u} [Field K] : ComponentEndpoint K 25 := by
  have hrQ : componentLogFloor 25 = (1539739918853 / 250000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 25 : ℝ) = 1539739918853 / 250000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 25) MME.DWZPositiveComponent314.parentProfile 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_314_original_profile_value (K := K))

theorem component_31 {K : Type u} [Field K] : ComponentEndpoint K 31 := by
  have hrQ : componentLogFloor 31 = (6159533826087 / 1000000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 31 : ℝ) = 6159533826087 / 1000000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 31) MME.DWZPositiveComponent413.parentProfile 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_413_original_profile_value (K := K))

theorem component_12 {K : Type u} [Field K] : ComponentEndpoint K 12 := by
  have hrQ : componentLogFloor 12 = (769869971361 / 125000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 12 : ℝ) = 769869971361 / 125000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 12) MME.DWZPositiveComponent134.parentProfile 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_134_original_profile_value (K := K))

theorem component_40 {K : Type u} [Field K] : ComponentEndpoint K 40 := by
  have hrQ : componentLogFloor 40 = (2096791354177 / 500000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 40 : ℝ) = 2096791354177 / 500000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 40) MME.DWZPositiveComponent611.parentProfile 160
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_611_original_profile_value (K := K))

theorem component_15 {K : Type u} [Field K] : ComponentEndpoint K 15 := by
  have hrQ : componentLogFloor 15 = (2096791343139 / 500000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 15 : ℝ) = 2096791343139 / 500000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 15) MME.DWZPositiveComponent161.parentProfile 8
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_161_original_profile_value (K := K))

theorem component_10 {K : Type u} [Field K] : ComponentEndpoint K 10 := by
  have hrQ : componentLogFloor 10 = (32056585721 / 7812500000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 10 : ℝ) = 32056585721 / 7812500000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 10) MME.DWZPositiveComponent116.parentProfile 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_116_original_profile_value (K := K))

theorem component_26 {K : Type u} [Field K] : ComponentEndpoint K 26 := by
  have hrQ : componentLogFloor 26 = (6676023212003 / 1000000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 26 : ℝ) = 6676023212003 / 1000000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 26) MME.DWZPositiveComponent323.parentProfile 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_323_original_profile_value (K := K))

theorem component_27 {K : Type u} [Field K] : ComponentEndpoint K 27 := by
  have hrQ : componentLogFloor 27 = (6676023499877 / 1000000000000 : ℚ) := by decide +kernel
  have hr : (componentLogFloor 27 : ℝ) = 6676023499877 / 1000000000000 := by rw [hrQ]; push_cast; rfl
  unfold ComponentEndpoint
  rw [hr]
  exact mme_dwz_prescribed_z_six_restriction_value_of_refined_profile
    _ _ _ (rawProfile 27) MME.DWZPositiveComponent332.parentProfile 2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
    (mme_dwz_positive_332_original_profile_value (K := K))

theorem solution {K : Type u} [Field K] :
    MME.DWZQ5GlobalLedger.AllComponentEndpoints K := by
  intro c
  fin_cases c
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 0 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 1 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 2 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 3 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 4 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 5 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 6 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 7 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 8 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 9 (by decide +kernel)
  · exact component_10
  · exact component_11
  · exact component_12
  · exact component_13
  · exact component_14
  · exact component_15
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 16 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 17 (by decide +kernel)
  · exact component_18
  · exact component_19
  · exact component_20
  · exact component_21
  · exact component_22
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 23 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 24 (by decide +kernel)
  · exact component_25
  · exact component_26
  · exact component_27
  · exact component_28
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 29 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 30 (by decide +kernel)
  · exact component_31
  · exact mme_dwz_positive_422_original_profile_value_at_ledger_rate
  · exact component_33
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 34 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 35 (by decide +kernel)
  · exact component_36
  · exact component_37
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 38 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 39 (by decide +kernel)
  · exact component_40
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 41 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 42 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 43 (by decide +kernel)
  · exact mme_dwz_q5_fourth_boundary_original_profile_endpoints 44 (by decide +kernel)
