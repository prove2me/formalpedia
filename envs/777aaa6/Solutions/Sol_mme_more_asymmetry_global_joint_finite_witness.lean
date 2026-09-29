-- Prove2me | solution 1 for mme_more_asymmetry_global_joint_finite_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T16:15:33.426877+00:00
-- url     : https://prove2.me/submissions/6b6f0edd-7664-47d0-918f-a4ef7a987155
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_released_global_six_region_numerical_extraction
import Theorems.Thm_mme_released_global_joint_start_ledger
import Theorems.Thm_mme_released_global_joint_recursive_continuation
open MME MME.GlobalCW MME.ReleasedGlobal
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

theorem solution :
    ∃ (n ell : ℕ) (D : GlobalCW.Start (4 * n) ell),
      0 < n ∧ 1 ≤ D.inputs ∧ 1 ≤ D.a * D.b * D.c ∧
      (n : ℝ) * ((281302098456 : ℝ) / 100000000000 - 1 / 1000000) +
        Real.log D.inputs ≤ D.logOutputs ∧
      (n : ℝ) * (3 * ((209612367517 : ℝ) / 100000000000) - 1 / 10000000) ≤
        Real.log ((D.a * D.b * D.c : ℕ) : ℝ) := by
  obtain ⟨eta,heta,hcontinue⟩ := mme_released_global_joint_recursive_continuation
  obtain ⟨eps,heps,hcap,k0,hglobal⟩ :=
    mme_released_global_six_region_numerical_extraction (K := ℚ) eta heta
  obtain ⟨k,hk0,hr⟩ := hcontinue eps heps hcap k0
  obtain ⟨hk,a,S,hS,hinputs,hpoly,houtputs⟩ := hglobal k hk0
  obtain ⟨R,hRi,hRd,hRrate,hRdim⟩ := hr hk a
  let D := jointStart (k^2) hk a eps S R
  obtain ⟨hDi,hpoly,ha,hb,hc,hD⟩ := mme_released_global_joint_start_ledger
    (k^2) hk a eps S hS R hRi ((1322355 : ℝ)/1000000) hRrate
  have hblock : 0 < blocks (k^2) := by
    unfold blocks MoreAsymmetryExactSeed.denominator
    exact Nat.mul_pos (by decide) hk
  refine ⟨6 * blocks (k^2),3,D,Nat.mul_pos (by decide) hblock,hDi,?_,?_,?_⟩
  · change 1 ≤ (jointStart (k^2) hk a eps S R).a *
      (jointStart (k^2) hk a eps S R).b * (jointStart (k^2) hk a eps S R).c
    rw [ha,hb,hc]
    exact hRd
  · have hcst : (281302098456 : ℝ)/100000000000 - 1/1000000 ≤
        2235998128/1500000000 + 1322355/1000000 := by norm_num
    calc
      _ ≤ (6 * blocks (k^2) : ℕ) *
          ((2235998128 : ℝ)/1500000000 + 1322355/1000000) + Real.log (D.inputs : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hcst (Nat.cast_nonneg (6 * blocks (k^2)))) le_rfl
      _ ≤ _ := hD
  · change (6 * blocks (k^2) : ℕ) *
      (3 * ((209612367517 : ℝ)/100000000000) - 1/10000000) ≤
        Real.log (((jointStart (k^2) hk a eps S R).a *
          (jointStart (k^2) hk a eps S R).b *
          (jointStart (k^2) hk a eps S R).c : ℕ) : ℝ)
    rw [ha,hb,hc]
    exact hRdim
