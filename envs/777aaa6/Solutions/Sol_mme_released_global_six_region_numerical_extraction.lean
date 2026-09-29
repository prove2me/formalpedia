-- Prove2me | solution 1 for mme_released_global_six_region_numerical_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T16:15:31.616268+00:00
-- url     : https://prove2.me/submissions/409e0d1c-ec0d-44a1-ad7d-fb2f04df13b9

import Theorems.Thm_mme_released_global_joint_window_family
import Theorems.Thm_mme_released_global_joint_window_extraction
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.ReleasedGlobal
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
universe u

theorem solution {K : Type u} [Field K] (eta : Fin 6 → ℝ) (heta : ∀ o, 0 < eta o) :
    ∃ eps : Fin 6 → ℝ, (∀ o, 0 < eps o) ∧ (∀ o, eps o ≤ eta o) ∧
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ hk : 0 < k^2,
      ∃ a : ∀ o : Fin 6, Reference o (k^2),
      ∃ S : ∀ o, Part (4 * blocks (k^2)) 3 (physicalWindow o (k^2) hk (a o) (eps o)),
        (∀ o, 1 ≤ (S o).inputs ∧ (S o).inputs ≤ (blocks (k^2)+1)^10935 ∧
          usableRate o * (blocks (k^2) : ℝ) + Real.log ((S o).inputs : ℝ) ≤ (S o).rate) ∧
        1 ≤ (∏ o, (S o).inputs) ∧ (∏ o, (S o).inputs) ≤ (blocks (k^2)+1)^65610 ∧
        ∃ outputs : ℕ,
          Real.exp ((6 * blocks (k^2) : ℕ) * ((2235998128 : ℝ)/1500000000)) *
            ((∏ o, (S o).inputs : ℕ) : ℝ) ≤ (outputs : ℝ) ∧
          Restrict (bigAdd (fun _ : Fin outputs ↦ tensor K (jointWindow (k^2) hk a eps)))
            (bigAdd (fun _ : Fin (∏ o, (S o).inputs) ↦
              (CWObj K 5).kronPow (4 * (6 * blocks (k^2))))) := by
  classical
  obtain ⟨eps,heps,hcap,k0,hglobal⟩ := mme_released_global_joint_window_family eta heta
  refine ⟨eps,heps,hcap,k0,?_⟩
  intro k hk0
  obtain ⟨hk,a,S,hS⟩ := hglobal k hk0
  have hi (o : Fin 6) : 0 < (S o).inputs := by have := (hS o).1; omega
  have hp : 0 < ∏ o, (S o).inputs := Finset.prod_pos (fun o _ ↦ hi o)
  have hprod : (∏ o, (S o).inputs) ≤ (blocks (k^2)+1)^65610 := by
    calc
      (∏ o, (S o).inputs) ≤ ∏ _ : Fin 6, (blocks (k^2)+1)^10935 :=
        Finset.prod_le_prod' (fun o _ ↦ (hS o).2.1)
      _ = _ := by simp [← pow_mul]
  have hsum : (∑ o : Fin 6, usableRate o) = (2235998128 : ℝ)/250000000 := by
    norm_num [usableRate,ReleasedGlobalNumeric.rateFloor,Fin.sum_univ_succ]
  have hlog : Real.log ((∏ o, (S o).inputs : ℕ) : ℝ) =
      ∑ o, Real.log ((S o).inputs : ℝ) := by
    rw [Nat.cast_prod]
    exact Real.log_prod (fun o _ ↦ by exact_mod_cast (hi o).ne')
  have hs := Finset.sum_le_sum (fun (o : Fin 6) (_ : o ∈ Finset.univ) ↦ (hS o).2.2)
  rw [Finset.sum_add_distrib,← Finset.sum_mul,hsum,← hlog] at hs
  have hr : (6 * blocks (k^2) : ℕ) * ((2235998128 : ℝ)/1500000000) +
      Real.log ((∏ o, (S o).inputs : ℕ) : ℝ) ≤ ∑ o, (S o).rate := by
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    nlinarith only [hs]
  obtain ⟨outputs,ho,hrestriction⟩ := mme_released_global_joint_window_extraction
    (K := K) (k^2) hk a eps S
  refine ⟨hk,a,S,hS,by omega,hprod,outputs,?_,hrestriction⟩
  have he := Real.exp_le_exp.mpr hr
  rw [Real.exp_add,Real.exp_log (by exact_mod_cast hp)] at he
  exact he.trans ho
