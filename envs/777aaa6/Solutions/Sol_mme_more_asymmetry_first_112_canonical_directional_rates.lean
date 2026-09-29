-- Prove2me | solution 1 for mme_more_asymmetry_first_112_canonical_directional_rates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:00:56.687332+00:00
-- url     : https://prove2.me/submissions/b8ceadce-0e30-4a83-b95d-f7ad808d5d74

import Theorems.Thm_mme_more_asymmetry_first_112_canonical_directional_extraction
import Theorems.Thm_mme_complete_split_112_outer_star_entropy_rate
import Theorems.Thm_mme_central_binomial_sqrt_loss_log_rate
import Theorems.Thm_mme_more_asymmetry_first_112_literal_directional_star_interface
import Mathlib.Tactic

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem profile_eq_of_probability_eq {ell : ℕ} (b c : Profile ell)
    (h : ∀ sigma, b.probability sigma = c.probability sigma) : b = c := by
  cases b
  cases c
  congr
  exact funext h

/-- Rates of the displayed matrix dimensions, not ambient tensor finranks. -/
private theorem exact_side_rates (m : ℕ) (hm : 0 < m) :
    Real.log ((5 ^ (2 * (1180582660953668517387 * m)) : ℕ) : ℝ) /
        (2 * (1180591620717411303424 * m : ℕ) : ℝ) =
      (1 - 2 * (8959763742786037 / 2361183241434822606848 : ℝ)) *
        Real.log 5 ∧
    Real.log ((5 ^ (2 * (8959763742786037 * m)) : ℕ) : ℝ) /
        (2 * (1180591620717411303424 * m : ℕ) : ℝ) =
      (2 * (8959763742786037 / 2361183241434822606848 : ℝ)) *
        Real.log 5 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  constructor <;> push_cast <;> rw [Real.log_pow] <;>
    push_cast <;> field_simp <;> ring

private theorem released_z_entropy :
    mme_modern_entropyBits
        (fun sigma : Fin 2 → Fin 3 =>
          (MoreAsymmetryFirstSlice.probability 0 2 sigma : ℝ)) =
      mme_modern_entropyBits
        ![(8959763742786037 / 2361183241434822606848 : ℝ),
          8959763742786037 / 2361183241434822606848,
          1 - 2 * (8959763742786037 / 2361183241434822606848 : ℝ)] := by
  classical
  unfold mme_modern_entropyBits
  congr 1
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 3)
    (fun sigma => Real.negMulLog (MoreAsymmetryFirstSlice.probability 0 2 sigma : ℝ))
    (fun pair => Real.negMulLog
      (MoreAsymmetryFirstSlice.probability 0 2 ![pair.1, pair.2] : ℝ))
    (by intro sigma; rfl)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ,
    MoreAsymmetryFirstSlice.probability, MoreAsymmetryFirstSlice.baseProbability,
    MoreAsymmetryFirstSlice.split0, add_comm]

theorem solution :
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
            ∀ (K : Type u) [Field K] (epsilon : ℝ≥0),
              Nonempty
                (CTensorOneHOneFamilyCertificate
                  (restrictedCanonicalPower K 5 beta epsilon (2 * N))
                  A H (5 ^ (4 * G + 2 * L))) ∧
              TensorObj.Restrict
                (TensorObj.bigAdd (starObj (grading K 5) family))
                (restrictedCanonicalPower K 5 beta epsilon (2 * N)) ∧
              ∀ a : Fin A,
                (∀ sigma : Fin 3 → Fin (H + 1),
                  sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
                    (starGrading (grading K 5) family a).blockTensor sigma = 0) ∧
                ∀ h : Fin H,
                  TensorObj.Isomorphic
                    (MMObj K (5 ^ (2 * G)) (5 ^ (2 * L)) (5 ^ (2 * G)))
                    ((starGrading (grading K 5) family a).blockSubtensor
                      (cTensorOneHOneAddress H h)) := by
  obtain ⟨beta, hbeta, C, _hC, hfamilies⟩ :=
    mme_more_asymmetry_first_112_canonical_directional_extraction.{u}
  obtain ⟨beta', hbeta', hstars⟩ :=
    mme_more_asymmetry_first_112_literal_directional_star_interface.{u}
  have hbetas : beta' = beta := by
    funext mode
    exact profile_eq_of_probability_eq _ _
      (fun sigma => (hbeta' mode sigma).trans (hbeta mode sigma).symm)
  subst beta'
  refine ⟨beta, hbeta, ?_⟩
  intro delta hdelta
  have he := mme_complete_split_112_outer_star_entropy_rate
    8959763742786037 1180582660953668517387 (by norm_num) C delta hdelta
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at he
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (mme_central_binomial_sqrt_loss_log_rate C delta hdelta)
  have hentropy :
      mme_modern_entropyBits (beta 2).probability =
        mme_modern_entropyBits
          ![(8959763742786037 / 2361183241434822606848 : ℝ),
            8959763742786037 / 2361183241434822606848,
            1 - 2 * (8959763742786037 / 2361183241434822606848 : ℝ)] := by
    rw [show (beta 2).probability =
      (fun sigma => (MoreAsymmetryFirstSlice.probability 0 2 sigma : ℝ)) from
        funext (hbeta 2)]
    exact released_z_entropy
  filter_upwards [hfamilies, he, eventually_ge_atTop n₀, eventually_gt_atTop 0]
    with m hm hme hmn hmpos
  dsimp only at hm hme ⊢
  obtain ⟨A, H, family, hApos, hH, hA, hAH, hcert⟩ := hm
  have hAHpos : (0 : ℝ) < (A : ℝ) * (H : ℝ) := by
    exact_mod_cast Nat.mul_pos hApos family.hHpos
  have hNm : n₀ ≤ 1180591620717411303424 * m := by omega
  have hlogAH := hn₀ (1180591620717411303424 * m) hNm
    ((A : ℝ) * (H : ℝ)) hAHpos (by simpa only [mul_assoc] using hAH)
  have hlogA := hme (A : ℝ) (by exact_mod_cast hApos) hA
  obtain ⟨hsideG, hsideL⟩ := exact_side_rates m hmpos
  refine ⟨A, H, family, hApos, hH, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hentropy, show (1 : ℝ) -
      2 * (8959763742786037 / 2361183241434822606848 : ℝ) =
        1180582660953668517387 / 1180591620717411303424 by norm_num] using hlogA
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlogAH
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsideG
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsideL
  · intro K inst epsilon
    exact ⟨hcert K epsilon, hstars K m A H family epsilon⟩
