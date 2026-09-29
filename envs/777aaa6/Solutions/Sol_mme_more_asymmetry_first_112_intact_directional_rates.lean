-- Prove2me | solution 1 for mme_more_asymmetry_first_112_intact_directional_rates
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:02:33.892799+00:00
-- url     : https://prove2.me/submissions/2817b3f9-30b9-4b70-aa06-e2b27a2057d1

import Definitions.Def_mme_more_asymmetry_first_112_profile_data
import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_coupled_Ctensor_packaging_data

import Theorems.Thm_mme_complete_split_112_canonical_power_restricts_from_intact
import Theorems.Thm_mme_more_asymmetry_first_112_canonical_directional_rates

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal

universe u

set_option autoImplicit false
namespace MME.MoreAsymmetryFirstSlice

/-- Integer complete-word histograms at the first-slice common denominator. -/
def exactHistogram (m : ℕ) (mode : Fin 3) (word : CompleteWord 2) : ℕ :=
  if mode.val = 2 then
    if ((word 0).val = 0 ∧ (word 1).val = 2) ∨
        ((word 0).val = 2 ∧ (word 1).val = 0) then 8959763742786037 * m
    else if (word 0).val = 1 ∧ (word 1).val = 1 then
      2 * (1180582660953668517387 * m) else 0
  else if ((word 0).val = 0 ∧ (word 1).val = 1) ∨
      ((word 0).val = 1 ∧ (word 1).val = 0) then 1180591620717411303424 * m
    else 0

/-- These histograms realize the released rational profile without rounding. -/
theorem exactHistogram_eq_scaled_probability (m : ℕ) (mode : Fin 3)
    (word : CompleteWord 2) :
    (exactHistogram m mode word : ℝ) =
      ((2 * (1180591620717411303424 * m) : ℕ) : ℝ) *
        (probability 0 mode word : ℝ) := by
  simp only [exactHistogram, probability, add_zero, baseProbability]
  split_ifs <;> push_cast <;> norm_num [split0] <;> ring

end MME.MoreAsymmetryFirstSlice

theorem solution :
    ∃ mu : ℕ → Fin 3 → CompleteWord 2 → ℕ,
      (∀ m mode sigma, (mu m mode sigma : ℝ) =
        ((2 * (1180591620717411303424 * m) : ℕ) : ℝ) *
          (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) ∧
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) ∧
      ∀ delta : ℝ, 0 < delta →
        ∀ᶠ m : ℕ in atTop,
          let N : ℕ := 1180591620717411303424 * m
          let L : ℕ := 8959763742786037 * m
          let G : ℕ := 1180582660953668517387 * m
          let p : ℝ := 8959763742786037 / 2361183241434822606848
          ∃ A H : ℕ, ∃ family : CWQ6PrimaryHashFamily N L G A H,
            0 < A ∧ H ≤ 4 ^ N ∧
            ((2 * N : ℕ) : ℝ) *
                (Real.log 2 * mme_modern_entropyBits (beta 2).probability - delta) ≤
              Real.log (A : ℝ) ∧
            ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
              Real.log ((A : ℝ) * (H : ℝ)) ∧
            Real.log ((5 ^ (2 * G) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) =
              (1 - 2 * p) * Real.log 5 ∧
            Real.log ((5 ^ (2 * L) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) =
              (2 * p) * Real.log 5 ∧
            ∀ (K : Type u) [Field K],
              Nonempty
                (CTensorOneHOneFamilyCertificate
                  (MME.RecursiveYZ.CWCells.unbroken K 5 2 (2 * N)
                    (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                    (fun i _ => mu m i))
                  A H (5 ^ (4 * G + 2 * L))) ∧
              TensorObj.Restrict
                (TensorObj.bigAdd (starObj (grading K 5) family))
                (MME.RecursiveYZ.CWCells.unbroken K 5 2 (2 * N)
                    (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                    (fun i _ => mu m i)) ∧
              ∀ a : Fin A,
                (∀ sigma : Fin 3 → Fin (H + 1),
                  sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
                    (starGrading (grading K 5) family a).blockTensor sigma = 0) ∧
                ∀ h : Fin H,
                  TensorObj.Isomorphic
                    (MMObj K (5 ^ (2 * G)) (5 ^ (2 * L)) (5 ^ (2 * G)))
                    ((starGrading (grading K 5) family a).blockSubtensor
                      (cTensorOneHOneAddress H h)) := by
  obtain ⟨beta, hbeta, hrates⟩ :=
    mme_more_asymmetry_first_112_canonical_directional_rates.{u}
  refine ⟨MoreAsymmetryFirstSlice.exactHistogram,
    MoreAsymmetryFirstSlice.exactHistogram_eq_scaled_probability, beta, hbeta, ?_⟩
  intro delta hdelta
  filter_upwards [hrates delta hdelta] with m hm
  rcases hm with ⟨A, H, family, hA, hH, hentropy, hproduct, hlong, hshort, hfamily⟩
  refine ⟨A, H, family, hA, hH, hentropy, hproduct, hlong, hshort, ?_⟩
  intro K _
  have hbridge := mme_complete_split_112_canonical_power_restricts_from_intact
    K 5 (2 * (1180591620717411303424 * m)) beta
    (MoreAsymmetryFirstSlice.exactHistogram m) (by
      intro i sigma
      rw [hbeta]
      exact MoreAsymmetryFirstSlice.exactHistogram_eq_scaled_probability m i sigma)
  obtain ⟨⟨cert⟩, hrestrict, hblocks⟩ := hfamily K 0
  exact ⟨⟨{
    star := cert.star
    restrict := cert.restrict.trans hbridge
    certificate := cert.certificate
  }⟩, hrestrict.trans hbridge, hblocks⟩

#print axioms solution
