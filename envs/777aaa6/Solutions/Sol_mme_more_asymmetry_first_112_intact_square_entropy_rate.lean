-- Prove2me | solution 1 for mme_more_asymmetry_first_112_intact_square_entropy_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:11:58.173177+00:00
-- url     : https://prove2.me/submissions/d55a13f6-68ae-468a-8eac-a704be46c232

import Theorems.Thm_mme_more_asymmetry_first_112_intact_square_extractions
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
universe u
set_option autoImplicit false

private theorem behrend_log_loss_bound (N H : ℕ) (hH : H ≤ 4 ^ N) :
    100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      200 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
  have hp : H + 1 ≤ 4 ^ (N + 1) := by
    have hpos : 0 < 4 ^ N := by positivity
    rw [pow_succ]
    omega
  have hlog : Real.log ((H + 1 : ℕ) : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((H + 1 : ℕ) : ℝ))
      (show ((H + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (N + 1) by exact_mod_cast hp)
    rw [Real.log_pow] at h
    have hfour : Real.log (4 : ℝ) ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log 4 := h
      _ ≤ ((N + 1 : ℕ) : ℝ) * 4 := mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = _ := mul_comm _ _
  have hl0 : 0 ≤ Real.log ((H + 1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hs : Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt hl0,
      Real.sq_sqrt (show (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by positivity),
      Real.sqrt_nonneg (Real.log ((H + 1 : ℕ) : ℝ)),
      Real.sqrt_nonneg ((N + 1 : ℕ) : ℝ)]
  linarith


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
          ∀ (K : Type u) [Field K], ∃ k : ℕ,
            TensorObj.Restrict
              (TensorObj.bigAdd (fun _ : Fin k =>
                MMObj K (5 ^ (4 * G + 2 * L)) (5 ^ (4 * G + 2 * L))
                  (5 ^ (4 * G + 2 * L))))
              (cyclicSymmetrization
                (MME.RecursiveYZ.CWCells.unbroken K 5 2 (2 * N)
                  (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                  (fun i _ => mu m i))) ∧
            ((2 * N : ℕ) : ℝ) *
                (Real.log 2 * (mme_modern_entropyBits (beta 2).probability + 2) - delta) ≤
              Real.log (k : ℝ) := by
  obtain ⟨mu, hmu, beta, hbeta, hrates⟩ :=
    mme_more_asymmetry_first_112_intact_square_extractions.{u}
  refine ⟨mu, hmu, beta, hbeta, ?_⟩
  intro delta hdelta
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (mme_log_sqrt_loss_eventually_le_linear 0 200 0 (delta / 2) (by positivity))
  filter_upwards [hrates (delta / 4) (by positivity), eventually_ge_atTop n₀]
    with m hm hmn
  obtain ⟨A, H, family, _, hH, _, _, _, _, hmatrix⟩ := hm
  dsimp only
  intro K _
  obtain ⟨k, hrestrict, _, hlog⟩ := hmatrix K
  refine ⟨k, hrestrict, ?_⟩
  have hloss := behrend_log_loss_bound (1180591620717411303424 * m) H hH
  have hbudget := hn₀ (1180591620717411303424 * m) (by omega)
  simp only [zero_mul, zero_add, add_zero] at hbudget
  simp only [Nat.cast_add, Nat.cast_one] at hloss hlog
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hlog hbudget hloss ⊢
  nlinarith only [hlog, hbudget, hloss]

#print axioms solution
