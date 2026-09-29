-- Prove2me | solution 1 for mme_more_asymmetry_first_112_intact_square_extractions
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:08:27.38391+00:00
-- url     : https://prove2.me/submissions/60c8e235-68eb-46b3-8242-9c58bc349ca5

import Theorems.Thm_mme_more_asymmetry_first_112_intact_directional_rates
import Theorems.Thm_mme_Ctensor_uniform_outer_family_square_extraction

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal
universe u
set_option autoImplicit false

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
          ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
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
            ∀ (K : Type u) [Field K], ∃ k : ℕ,
              TensorObj.Restrict
                (TensorObj.bigAdd (fun _ : Fin k =>
                  MMObj K (5 ^ (4 * G + 2 * L)) (5 ^ (4 * G + 2 * L))
                    (5 ^ (4 * G + 2 * L))))
                (cyclicSymmetrization
                  (MME.RecursiveYZ.CWCells.unbroken K 5 2 (2 * N)
                    (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                    (fun i _ => mu m i))) ∧
              (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
                Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))) ≤
                (k : ℝ) ∧
              ((2 * N : ℕ) : ℝ) *
                  (Real.log 2 * (mme_modern_entropyBits (beta 2).probability + 2) -
                    3 * delta) -
                100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))) ≤ Real.log (k : ℝ) := by
  classical
  obtain ⟨mu, hmu, beta, hbeta, hrates⟩ :=
    mme_more_asymmetry_first_112_intact_directional_rates.{u}
  refine ⟨mu, hmu, beta, hbeta, ?_⟩
  intro delta hdelta
  filter_upwards [hrates delta hdelta] with m hm
  rcases hm with ⟨A, H, family, hA, hH, hentropy, hproduct, hlong, hshort, hfamily⟩
  refine ⟨A, H, family, hA, hH, hentropy, hproduct, hlong, hshort, ?_⟩
  intro K _
  obtain ⟨_, hrestrict, hblocks⟩ := hfamily K
  let G := 1180582660953668517387 * m
  let L := 8959763742786037 * m
  have hvolume : 5 ^ (2 * G) * 5 ^ (2 * L) * 5 ^ (2 * G) =
      (5 : ℕ) ^ (4 * G + 2 * L) := by
    simp only [← pow_add]
    congr 1
    omega
  let cert : CTensorOneHOneFamilyCertificate _ A H (5 ^ (4 * G + 2 * L)) := {
    star := starObj (grading K 5) family
    restrict := hrestrict
    certificate := fun a => {
      grading := starGrading (grading K 5) family a
      supported := (hblocks a).1
      m := fun _ => 5 ^ (2 * G)
      n := fun _ => 5 ^ (2 * L)
      p := fun _ => 5 ^ (2 * G)
      component := (hblocks a).2
      common_volume := fun _ => hvolume
    }
  }
  obtain ⟨k, hk, hcount⟩ := mme_Ctensor_uniform_outer_family_square_extraction
    cert (5 ^ (2 * G)) (5 ^ (2 * L)) (5 ^ (2 * G))
    (fun _ _ => ⟨rfl, rfl, rfl⟩) family.hHpos
  refine ⟨k, ?_, hcount, ?_⟩
  · simpa only [hvolume] using hk
  · have hAr : (0 : ℝ) < A := by exact_mod_cast hA
    have hHr : (0 : ℝ) < H := by exact_mod_cast family.hHpos
    have hpositive : 0 < (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
        Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))) := by positivity
    have hlog := Real.log_le_log hpositive hcount
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_exp] at hlog
    rw [Real.log_mul (ne_of_gt hAr) (ne_of_gt hHr)] at hproduct
    norm_num only [Nat.cast_ofNat] at hlog
    nlinarith only [hlog, hentropy, hproduct]


#print axioms solution
