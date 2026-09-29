-- Prove2me | solution 1 for mme_released_global_joint_start_ledger
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T16:15:30.513492+00:00
-- url     : https://prove2.me/submissions/25e43919-304a-4c4e-94c3-0f54373b8a27

import Definitions.Def_mme_released_global_joint_interface
open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RegionRealization MME.ReleasedGlobal
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
attribute [local irreducible] frame windowGood physicalPart

theorem solution (k : ℕ) (hk : 0 < k)
    (a : ∀ o : Fin 6, Reference o k) (eps : Fin 6 → ℝ)
    (S : ∀ o, Part (4 * blocks k) 3 (physicalWindow o k hk (a o) (eps o)))
    (hS : ∀ o, 1 ≤ (S o).inputs ∧ (S o).inputs ≤ (blocks k+1)^10935 ∧
      usableRate o * (blocks k : ℝ) + Real.log ((S o).inputs : ℝ) ≤ (S o).rate)
    (R : LogJointRecipe (4 * (6 * blocks k)) 3 (jointWindow k hk a eps))
    (hR : 1 ≤ R.inputs) (rho : ℝ)
    (hrate : (6 * blocks k : ℕ) * rho + Real.log (R.inputs : ℝ) ≤ R.logOutputs) :
    let D := jointStart k hk a eps S R
    1 ≤ D.inputs ∧ D.inputs ≤ (blocks k+1)^65610 * R.inputs ∧
      D.a = R.a ∧ D.b = R.b ∧ D.c = R.c ∧
      (6 * blocks k : ℕ) * ((2235998128 : ℝ)/1500000000 + rho) +
        Real.log (D.inputs : ℝ) ≤ D.logOutputs := by
  classical
  have hi (o : Fin 6) : 0 < (S o).inputs := by have := (hS o).1; omega
  have hp : 0 < ∏ o, (S o).inputs := Finset.prod_pos (fun o _ ↦ hi o)
  have hprod : (∏ o, (S o).inputs) ≤ (blocks k+1)^65610 := by
    calc
      (∏ o, (S o).inputs) ≤ ∏ _ : Fin 6, (blocks k+1)^10935 :=
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
  change 1 ≤ (∏ o, (S o).inputs) * R.inputs ∧
    (∏ o, (S o).inputs) * R.inputs ≤ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hp.ne' (by omega)),
    Nat.mul_le_mul_right R.inputs hprod,rfl,rfl,rfl,?_⟩
  change (6 * blocks k : ℕ) * ((2235998128 : ℝ)/1500000000 + rho) +
    Real.log (((∏ o, (S o).inputs) * R.inputs : ℕ) : ℝ) ≤
      (∑ o, (S o).rate) + R.logOutputs
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hrate ⊢
  rw [Real.log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast (show R.inputs ≠ 0 by omega))]
  nlinarith only [hs,hrate]
