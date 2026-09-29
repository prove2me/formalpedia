-- Prove2me | solution 1 for mme_more_asymmetry_global_graded_finite_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T16:41:06.898126+00:00
-- url     : https://prove2.me/submissions/24a3bc4c-0b21-4ea2-99a0-7fabcd02f222

import Theorems.Thm_mme_released_global_joint_window_family
import Theorems.Thm_mme_released_global_graded_joint_recursive_continuation
import Definitions.Def_mme_global_CW_graded_start_data
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

theorem solution :
    ∃ (n ell : ℕ) (D : GlobalCW.StartG (4 * n) ell),
      0 < n ∧ 1 ≤ D.inputs ∧ 1 ≤ D.a * D.b * D.c ∧
      (n : ℝ) * ((281302098456 : ℝ) / 100000000000 - 1 / 1000000) +
        Real.log D.inputs ≤ D.logOutputs ∧
      (n : ℝ) * (3 * ((209612367517 : ℝ) / 100000000000) - 1 / 10000000) ≤
        Real.log ((D.a * D.b * D.c : ℕ) : ℝ) := by
  classical
  obtain ⟨eta, heta, hcont⟩ := mme_released_global_graded_joint_recursive_continuation
  obtain ⟨eps, heps, hcap, k0, hglobal⟩ := mme_released_global_joint_window_family eta heta
  obtain ⟨k, hk0, hk⟩ := hcont eps heps hcap k0
  obtain ⟨hkpos, a, S, hS⟩ := hglobal k hk0
  obtain ⟨R, hR1, habc, hrate, hdim⟩ := hk hkpos a
  let D : StartG (4 * (6 * blocks (k^2))) 3 :=
    { parts := 6
      size := fun _ ↦ 4 * blocks (k^2)
      positions := jointPositions (k^2)
      T := fun o ↦ physicalWindow o (k^2) hkpos (a o) (eps o)
      steps := S
      Q := jointWindow (k^2) hkpos a eps
      target := fun _ _ h ↦ h
      next := R }
  have hb : 0 < blocks (k^2) := by
    unfold blocks; exact Nat.mul_pos (pow_pos (by unfold MoreAsymmetryExactSeed.denominator; norm_num) 5) hkpos
  have hi (o : Fin 6) : 0 < (S o).inputs := by have := (hS o).1; omega
  have hp : 0 < ∏ o, (S o).inputs := Finset.prod_pos (fun o _ ↦ hi o)
  refine ⟨6 * blocks (k^2), 3, D, by omega, ?_, habc, ?_, hdim⟩
  · change 1 ≤ (∏ o, (S o).inputs) * R.inputs
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne' (by omega))
  · have hsum : (∑ o : Fin 6, usableRate o) = (2235998128 : ℝ)/250000000 := by
      norm_num [usableRate,ReleasedGlobalNumeric.rateFloor,Fin.sum_univ_succ]
    have hlog : Real.log ((∏ o, (S o).inputs : ℕ) : ℝ) =
        ∑ o, Real.log ((S o).inputs : ℝ) := by
      rw [Nat.cast_prod]
      exact Real.log_prod (fun o _ ↦ by exact_mod_cast (hi o).ne')
    have hs := Finset.sum_le_sum (fun (o : Fin 6) (_ : o ∈ Finset.univ) ↦ (hS o).2.2)
    rw [Finset.sum_add_distrib,← Finset.sum_mul,hsum,← hlog] at hs
    have hB0 : (0 : ℝ) ≤ (blocks (k^2) : ℝ) := Nat.cast_nonneg _
    change ((6 * blocks (k^2) : ℕ) : ℝ) * ((281302098456 : ℝ) / 100000000000 - 1 / 1000000) +
      Real.log (((∏ o, (S o).inputs) * R.inputs : ℕ) : ℝ) ≤
        (∑ o, (S o).rate) + R.logOutputs
    rw [Nat.cast_mul (∏ o, (S o).inputs) R.inputs,
      Real.log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast (show R.inputs ≠ 0 by omega))]
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hrate ⊢
    linarith
