-- Prove2me | solution 1 for mme_tau_value_below_base_le_of_asymptoticRank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:14:06.365225+00:00
-- url     : https://prove2.me/submissions/e7b1edcb-f743-4a1c-ad79-da5d5d834c0a

import Theorems.Thm_mme_tau_value_le_of_asymptoticRank_le

open MME

universe u

/-!
# Passing from all strict tau-value lower bounds to the endpoint

The existing rank bridge applies to an attained value.  For a base that is
only approached from below, a midpoint contradiction is enough; no endpoint
attainment or topological closure theorem is needed.
-/

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {B R : ℝ}
    (hR_one : 1 ≤ R)
    (hR : tensorAsymptoticRank T ≤ R)
    (hbelow : ∀ V : ℝ, 1 ≤ V → V < B →
      HasTauValueAtLeast T (matMulExp_strassen K / 3) V) :
    B ≤ R := by
  by_contra hBR
  rw [not_le] at hBR
  let V : ℝ := (B + R) / 2
  have hRV : R < V := by
    dsimp [V]
    linarith
  have hVB : V < B := by
    dsimp [V]
    linarith
  have hV_one : 1 ≤ V := hR_one.trans hRV.le
  have hV := hbelow V hV_one hVB
  have hVR : V ≤ R :=
    mme_tau_value_le_of_asymptoticRank_le
      (le_trans (by norm_num) hR_one) hV_one hR hV
  exact (not_le_of_gt hRV) hVR
