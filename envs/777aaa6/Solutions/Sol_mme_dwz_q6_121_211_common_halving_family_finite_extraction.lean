-- Prove2me | solution 1 for mme_dwz_q6_121_211_common_halving_family_finite_extraction
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:39:46.89713+00:00
-- url     : https://prove2.me/submissions/d4d212b5-e5dd-407b-a406-60c31ff1d90f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mme_dwz_q6_121_211_common_halving_primary_hash_family_paired_Ctensor_certificate
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap
import Theorems.Thm_mme_behrend_log_loss_absorbed_sqrt

open MME BigOperators
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ)
    (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (MME.DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hHbound : H ≤ 4 ^ (MME.DWZTable2Counts.component s * m)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (restrictedComponentPower K s m)) ∧
      (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          ((((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau) *
          Real.exp (-200 * Real.sqrt
            ((((MME.DWZTable2Counts.component s * m) + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨stars⟩ :=
    mme_dwz_q6_121_211_common_halving_primary_hash_family_paired_Ctensor_certificate
      (K := K) s hs m L G A H family halving
  obtain ⟨q, a, b, c, hrestrict, hcount, hvolume⟩ :=
    mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
      stars family.hHpos
  refine ⟨q, a, b, c, ?_, ?_⟩
  · exact TensorObj.Restrict.trans hrestrict
      (mme_sixSymmetrization_isomorphic_cyclic_paired_swap
        (restrictedComponentPower K s m)).2
  · let v : ℕ := 6 ^ (4 * G + 2 * L)
    let w : ℝ := (((v ^ 3 : ℕ) : ℝ) ^ tau)
    let behrend : ℝ := Real.exp (-100 *
      Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))
    let sourceLoss : ℝ := Real.exp (-200 * Real.sqrt
      ((((MME.DWZTable2Counts.component s * m) + 1 : ℕ) : ℝ)))
    have habsorb : sourceLoss ≤ behrend := by
      simpa only [sourceLoss, behrend] using
        mme_behrend_log_loss_absorbed_sqrt
          (MME.DWZTable2Counts.component s * m) H hHbound
    have hw : 0 ≤ w := by
      dsimp [w]
      positivity
    have hcapacity :
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) * sourceLoss ≤
          (q : ℝ) := by
      calc
        (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) * sourceLoss =
            (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 * sourceLoss) := by
              norm_num
              ring
        _ ≤ (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 * behrend) := by
              gcongr
        _ ≤ (q : ℝ) := by
              simpa only [behrend] using hcount
    have hsum :
        (∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) =
          (q : ℝ) * w := by
      dsimp [w, v]
      simp_rw [hvolume]
      simp
    change (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) * w * sourceLoss ≤ _
    rw [hsum]
    calc
      (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) * w * sourceLoss =
          ((((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) * sourceLoss) * w := by
            ring
      _ ≤ (q : ℝ) * w := mul_le_mul_of_nonneg_right hcapacity hw
