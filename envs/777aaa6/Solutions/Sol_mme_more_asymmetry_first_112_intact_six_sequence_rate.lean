-- Prove2me | solution 1 for mme_more_asymmetry_first_112_intact_six_sequence_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:21:38.88931+00:00
-- url     : https://prove2.me/submissions/9852fa2e-fa8e-4288-8c7c-54858b23dbe7

import Theorems.Thm_mme_more_asymmetry_first_112_intact_square_extractions
import Theorems.Thm_mme_finite_MM_extraction_swap_double
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging MME.DWZRestrictedValue
open scoped BigOperators
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


private theorem positive_square_entropy_rate :
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
          ∀ (K : Type u) [Field K], ∃ k : ℕ, 0 < k ∧
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
  obtain ⟨A, H, family, hA, hH, _, _, _, _, hmatrix⟩ := hm
  dsimp only
  intro K _
  obtain ⟨k, hrestrict, hcount, hlog⟩ := hmatrix K
  have hAr : (0 : ℝ) < A := by exact_mod_cast hA
  have hHr : (0 : ℝ) < H := by exact_mod_cast family.hHpos
  have hkr : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hcount
  refine ⟨k, by exact_mod_cast hkr, hrestrict, ?_⟩
  have hloss := behrend_log_loss_bound (1180591620717411303424 * m) H hH
  have hbudget := hn₀ (1180591620717411303424 * m) (by omega)
  simp only [zero_mul, zero_add, add_zero] at hbudget
  simp only [Nat.cast_add, Nat.cast_one] at hloss hlog
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hlog hbudget hloss ⊢
  nlinarith only [hlog, hbudget, hloss]


private theorem six_square_weight (m : ℕ) (tau : ℝ) :
    let N := 1180591620717411303424 * m
    let L := 8959763742786037 * m
    let G := 1180582660953668517387 * m
    let d := 5 ^ (4 * G + 2 * L)
    (((d * d * (d * d) * (d * d) : ℕ) : ℝ) ^ tau) =
      Real.exp (((4 * N : ℕ) : ℝ) *
        (3 * tau * (2 - 2 * (MoreAsymmetryFirstSlice.split0 : ℝ)) * Real.log 5)) := by
  dsimp only
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1
  push_cast
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  norm_num [MoreAsymmetryFirstSlice.split0]
  ring

/-- The intact first-slice sequence attains its six-symmetric component endpoint. -/
theorem solution :
    ∃ mu : ℕ → Fin 3 → CompleteWord 2 → ℕ,
      (∀ m mode sigma, (mu m mode sigma : ℝ) =
        ((2 * (1180591620717411303424 * m) : ℕ) : ℝ) *
          (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) ∧
      ∀ (K : Type u) [Field K] (tau : ℝ),
        HasSixSequenceRate TensorObj.Restrict
          (fun m => MME.RecursiveYZ.CWCells.unbroken K 5 2
            (2 * (1180591620717411303424 * m)) (Equiv.refl _)
            (fun _ => Unit.unit) (fun _ => ![1, 1, 2]) (fun i _ => mu m i))
          (fun m => 2 * (1180591620717411303424 * m)) tau
          (Real.exp ((Real.log 2 *
              (mme_modern_entropyBits
                (fun word => (MoreAsymmetryFirstSlice.probability 0 2 word : ℝ)) + 2) +
            3 * tau * (2 - 2 * (MoreAsymmetryFirstSlice.split0 : ℝ)) * Real.log 5) / 3)) := by
  obtain ⟨mu, hmu, beta, hbeta, hrates⟩ := positive_square_entropy_rate.{u}
  refine ⟨mu, hmu, ?_⟩
  intro K _ tau
  let E := Real.log 2 * (mme_modern_entropyBits
    (fun word => (MoreAsymmetryFirstSlice.probability 0 2 word : ℝ)) + 2)
  let W := 3 * tau * (2 - 2 * (MoreAsymmetryFirstSlice.split0 : ℝ)) * Real.log 5
  refine ⟨(Real.exp_pos _).le, ?_⟩
  intro v hv hvlt cutoff
  have hvlog : Real.log v < (E + W) / 3 := (Real.log_lt_iff_lt_exp hv).2 hvlt
  let delta := (E + W - 3 * Real.log v) / 2
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hrates delta hdelta)
  let m := max M cutoff
  obtain ⟨k, hkpos, hrestrict, hlog⟩ := hM m (le_max_left _ _) K
  let N := 1180591620717411303424 * m
  let L := 8959763742786037 * m
  let G := 1180582660953668517387 * m
  let d := 5 ^ (4 * G + 2 * L)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hdouble := mme_finite_MM_extraction_swap_double
    (fun _ : Fin k => d) (fun _ : Fin k => d) (fun _ : Fin k => d) hrestrict
  refine ⟨m, le_max_right _ _, ?_, k * k,
    (fun _ => d * d), (fun _ => d * d), (fun _ => d * d), hdouble, ?_⟩
  · dsimp only [m]
    omega
  · rw [show (beta 2).probability =
        (fun word => (MoreAsymmetryFirstSlice.probability 0 2 word : ℝ)) from
      funext (hbeta 2)] at hlog
    change ((2 * N : ℕ) : ℝ) * (E - delta) ≤ Real.log (k : ℝ) at hlog
    have hweight := six_square_weight m tau
    change (((d * d * (d * d) * (d * d) : ℕ) : ℝ) ^ tau) =
      Real.exp (((4 * N : ℕ) : ℝ) * W) at hweight
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hweight, Nat.cast_mul]
    have hcount : (k : ℝ) * k = Real.exp (2 * Real.log (k : ℝ)) := by
      rw [two_mul, Real.exp_add, Real.exp_log hkr]
    rw [hcount, ← Real.exp_add]
    have hvpow : v ^ (6 * (2 * N)) =
        Real.exp (((6 * (2 * N) : ℕ) : ℝ) * Real.log v) := by
      rw [Real.exp_nat_mul, Real.exp_log hv]
    change v ^ (6 * (2 * N)) ≤ _
    rw [hvpow]
    apply Real.exp_le_exp.mpr
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hlog ⊢
    have hnonneg : 0 ≤ (N : ℝ) * delta := mul_nonneg (by positivity) hdelta.le
    dsimp only [delta] at hlog hnonneg
    nlinarith only [hlog, hnonneg]

#print axioms solution
