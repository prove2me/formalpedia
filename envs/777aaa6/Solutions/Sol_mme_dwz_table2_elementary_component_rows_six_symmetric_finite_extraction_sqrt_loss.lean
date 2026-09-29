-- Prove2me | solution 1 for mme_dwz_table2_elementary_component_rows_six_symmetric_finite_extraction_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T20:44:38.997959+00:00
-- url     : https://prove2.me/submissions/41ac7d5e-7bd5-4626-9748-5338fd1a925d

import Theorems.Thm_mme_dwz_table2_elementary_component_rows_one_MM_finite_extraction_sqrt_loss
import Theorems.Thm_mme_sixSymmetrization_restrict
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_sixSymmetrization_MMObj_isomorphic

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.ElementaryRowsFromOneMM

theorem bigAdd_one_isomorphic
    {K : Type u} [Field K] (T : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun _ : Fin 1 ↦ T)) T := by
  apply (TensorQ.toQ_eq_iff).1
  rw [TensorQ.toQ_bigAdd]
  simp

end MME.ElementaryRowsFromOneMM

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s.val ≤ 8 ∨ s = 11) →
          ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd (fun j => MMObj K (A j) (B j) (Cdim j)))
              (sixSymmetrization (restrictedComponentPower K s m)) ∧
            (((componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨C, hC, hrows⟩ :=
    mme_dwz_table2_elementary_component_rows_one_MM_finite_extraction_sqrt_loss
      (K := K) tau htau
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrows] with m hm
  intro s hs
  obtain ⟨a, b, c, habc, hweight⟩ := hm s hs
  let v : ℕ := a * b * c
  let Q : TensorObj K 3 := MMObj K (v ^ 2) (v ^ 2) (v ^ 2)
  have hsingle := MME.ElementaryRowsFromOneMM.bigAdd_one_isomorphic Q
  have hsixMM := mme_sixSymmetrization_MMObj_isomorphic
    (K := K) a b c
  have hsixRestrict := mme_sixSymmetrization_restrict habc
  have hrestrict :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun _ : Fin 1 ↦ Q))
        (sixSymmetrization (restrictedComponentPower K s m)) :=
    TensorObj.Restrict.trans hsingle.1
      (TensorObj.Restrict.trans hsixMM.2 hsixRestrict)
  refine ⟨1, (fun _ ↦ v ^ 2), (fun _ ↦ v ^ 2),
    (fun _ ↦ v ^ 2), ?_, ?_⟩
  · simpa only [Q] using hrestrict
  · simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, v] using hweight
