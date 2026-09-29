-- Prove2me | solution 1 for mme_stothers_phi233_low_exponent_value_below
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T08:07:59.175693+00:00
-- url     : https://prove2.me/submissions/5215e0ef-bffe-4617-96b2-38186a55996f

import Definitions.Def_mme_permutation
import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_tau_value
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_MMObj_permObj_cyclic_sq
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_CW_coupled_high_block_restrict
import Theorems.Thm_mme_stothers_phi233_fine_component_restrictions
import Theorems.Thm_mme_CW_fourth_fine_block_restrict_coarse_block
import Theorems.Thm_mme_MMObj_square_scalar_value_below
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict
import Mathlib.Tactic

open MME MME.StothersFourth
universe u
set_option autoImplicit false

/-- A coarse bound sufficient for the scalar-extraction route below exponent one third. -/
theorem phi233_classValue_low_exponent_bound (tau : ℝ) (htau : 3 * tau ≤ 1) :
    classValue 6 tau 9 < (1296 : ℝ) ^ 2 := by
  let x : ℝ := (6 : ℝ) ^ (3 * tau)
  have hx : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hx6 : x ≤ 6 := by
    simpa [x] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 6) htau
  have hE : E 6 tau ≤ 12 := by
    simpa [E] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 12) htau
  have hE0 : 0 < E 6 tau := by unfold E; positivity
  have hL : L 6 tau = 4 * x * (x + 2) := rfl
  have hL0 : 0 < L 6 tau := by rw [hL]; positivity
  have hL192 : L 6 tau ≤ 192 := by rw [hL]; nlinarith
  have hratio : (38 / 6 : ℝ) ^ (3 * tau) ≤ 38 / 6 := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 38 / 6) htau
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 38) (by norm_num : (0 : ℝ) ≤ 6)] at hratio
  have hH : H 6 tau ≤ L 6 tau := by
    have hh : H 6 tau = (38 : ℝ) ^ (3 * tau) := by norm_num [H]
    change (38 : ℝ) ^ (3 * tau) / x ≤ 38 / 6 at hratio
    have h38 := (div_le_iff₀ hx).mp hratio
    rw [hh, hL]
    nlinarith
  have hsum : (E 6 tau + L 6 tau) ^ 2 ≤ (204 : ℝ) ^ 2 := by nlinarith
  have hc : classValue 6 tau 9 =
      4 * (E 6 tau + L 6 tau) ^ 2 * (2 * H 6 tau + L 6 tau) / L 6 tau := by
    rfl
  rw [hc]
  apply (div_le_iff₀ hL0).2 ?_ |>.trans_lt (by norm_num : (499392 : ℝ) < 1296 ^ 2)
  have hfac : 2 * H 6 tau + L 6 tau ≤ 3 * L 6 tau := by linarith
  have hm := mul_le_mul_of_nonneg_left hfac (by positivity : 0 ≤ 4 * (E 6 tau + L 6 tau) ^ 2)
  nlinarith [mul_le_mul_of_nonneg_right hsum (le_of_lt hL0)]


private theorem kron_restrict_pair {K : Type u} [Field K]
    {X X' Y Y' : TensorObj K 3} (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  let P := TensorQ.tensorStrassen K 3 (by omega)
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have h1 := P.mul_right _ _ hx (TensorQ.toQ Y)
  have h2 := P.mul_right _ _ hy (TensorQ.toQ X')
  have h2' : P.le (TensorQ.toQ X' * TensorQ.toQ Y)
      (TensorQ.toQ X' * TensorQ.toQ Y') := by simpa only [mul_comm] using h2
  exact P.le_trans _ _ _ h1 h2'

/-- A concrete high-high fine block supplies an exponent-independent scalar bound. -/
theorem phi233_restrict_square_1296 {K : Type u} [Field K] :
    TensorObj.Restrict (MMObj K 1296 1296 1296)
      (cyclicSymmetrization (cwFourthConstituent K 6 2 3 3)) := by
  have hh := mme_CW_coupled_high_block_restrict (K := K) 6
  have hp := TensorObj.permObj_restrict (cyclicPerm.trans cyclicPerm) hh
  have hi := mme_MMObj_permObj_cyclic_sq (K := K) 6 1 6
  have hprod := kron_restrict_pair hh (hi.2.trans hp)
  have hmm := (MMObj_kron_iso (K := K) 6 1 6 1 6 6).2.trans hprod
  have hf := (mme_stothers_phi233_fine_component_restrictions (K := K) 6).2.2.2.2.1
  have hc := mme_CW_fourth_fine_block_restrict_coarse_block (K := K) 6
    1 1 2 1 2 1 (cwFourthBlockType 2 3 3) (by intro i; fin_cases i <;> rfl)
  have hr : TensorObj.Restrict (MMObj K 6 6 36) (cwFourthConstituent K 6 2 3 3) :=
    hmm.trans (hf.trans hc)
  have hcyc := mme_cyclicSymmetrization_mono_restrict hr
  have hm := (mme_MMObj_cyclicSymmetrization_iso (K := K) 6 6 36).2
  exact hm.trans hcyc


/-- The low-exponent part of the unrestricted phi233 value claim. -/
theorem solution
    {K : Type u} [Field K] (tau V : ℝ) (htau : 3 * tau ≤ 1)
    (hV : 0 ≤ V) (hVlt : V < classValue 6 tau 9) :
    HasTauValueAtLeast (cyclicSymmetrization
      (cwFourthConstituent K 6 2 3 3)) tau V := by
  have hv := mme_MMObj_square_scalar_value_below (K := K) 1296 tau V hV
    (hVlt.trans (phi233_classValue_low_exponent_bound tau htau))
  exact mme_HasTauValueAtLeast_mono_restrict phi233_restrict_square_1296 hv

