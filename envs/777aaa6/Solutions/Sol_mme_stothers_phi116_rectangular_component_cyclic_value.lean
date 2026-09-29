-- Prove2me | solution 1 for mme_stothers_phi116_rectangular_component_cyclic_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:51:48.842534+00:00
-- url     : https://prove2.me/submissions/5aeafbbc-919b-4a8e-ba98-f8f6fd6c7e96

import Mathlib.Tactic
import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_MMObj_tau_value
import Theorems.Thm_mme_CW_coupled_cyclic_high_MM_restrict
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (tau : ℝ) :
    HasTauValueAtLeast (cyclicSymmetrization (MMObj K 12 1 12)) tau
      (MME.StothersFourth.E 6 tau ^ (2 : ℕ)) := by
  have h := mme_HasTauValueAtLeast_mono_restrict
    (mme_CW_coupled_cyclic_high_MM_restrict (K := K) 12)
    (mme_MMObj_tau_value (K := K) 144 144 144 tau)
  have heq :
      ((((144 * 144 * 144 : ℕ) : ℝ) ^ tau)) =
        MME.StothersFourth.E 6 tau ^ (2 : ℕ) := by
    unfold MME.StothersFourth.E
    norm_num only [Nat.cast_ofNat, Nat.reduceMul]
    rw [show (2985984 : ℝ) = 12 ^ (6 : ℕ) by norm_num]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 12) 6 tau]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 12) (3 * tau) 2]
    congr 1
    ring
  rwa [heq] at h
