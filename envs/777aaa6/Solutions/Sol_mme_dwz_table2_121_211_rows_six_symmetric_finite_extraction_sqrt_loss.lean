-- Prove2me | solution 1 for mme_dwz_table2_121_211_rows_six_symmetric_finite_extraction_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:39:58.680689+00:00
-- url     : https://prove2.me/submissions/6b0f61b6-9559-4ade-b2fc-d30ef67f46fc

import Theorems.Thm_mme_dwz_q6_121_211_source_faithful_coupled_sqrt_loss_extractions
import Theorems.Thm_mme_dwz_q6_121_211_componentBase_cube
import Definitions.Def_mme_dwz_square_data

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 13 ∨ s = 14) →
          ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd (fun j ↦ MMObj K (A j) (B j) (Cdim j)))
              (sixSymmetrization (restrictedComponentPower K s m)) ∧
            (((componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨C, hC, hextract⟩ :=
    mme_dwz_q6_121_211_source_faithful_coupled_sqrt_loss_extractions
      (K := K) tau htau
  refine ⟨C, hC, ?_⟩
  filter_upwards [hextract] with m hm
  intro s hs
  obtain ⟨q, A, B, Cdim, hrestrict, hrate⟩ := hm s hs
  refine ⟨q, A, B, Cdim, hrestrict, ?_⟩
  let raw : ℝ :=
    4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
  let N : ℕ := MME.DWZTable2Counts.component s * m
  have hcube : componentBase tau s ^ (3 : ℕ) = raw := by
    rcases hs with rfl | rfl
    · exact mme_dwz_q6_121_211_componentBase_cube tau
    · simpa only [componentBase, raw] using
        mme_dwz_q6_121_211_componentBase_cube tau
  have hpower :
      ((componentBase tau s) ^ N) ^ (6 : ℕ) = raw ^ (2 * N) := by
    calc
      ((componentBase tau s) ^ N) ^ (6 : ℕ) =
          (componentBase tau s) ^ (N * 6) := by
            exact (pow_mul (componentBase tau s) N 6).symm
      _ = (componentBase tau s) ^ (3 * (2 * N)) := by
        congr 1
        omega
      _ = ((componentBase tau s) ^ (3 : ℕ)) ^ (2 * N) := by
        exact pow_mul (componentBase tau s) 3 (2 * N)
      _ = raw ^ (2 * N) := by rw [hcube]
  change ((componentBase tau s) ^ N) ^ (6 : ℕ) *
      Real.exp (-C * Real.sqrt
        (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤ _
  rw [hpower]
  simpa only [raw, N] using hrate
